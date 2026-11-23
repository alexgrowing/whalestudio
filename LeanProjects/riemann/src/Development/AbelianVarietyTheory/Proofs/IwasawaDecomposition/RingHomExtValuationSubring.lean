import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

namespace GlobalTheory.LocM.MapComp

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {k N N' : Type} [Field k] [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N'] {m : ℕ}

def IsBas (M : Submodule k N) (b : Fin m → N) : Prop :=
  (∀ i, b i ∈ M) ∧ ∀ n ∈ M, ∃! a : Fin m → k, n = ∑ j, a j • b j

theorem isBas_iff (M : Submodule k N) (b : Fin m → N) :
    IsBas M b ↔ Function.Injective (Fintype.linearCombination k b) ∧
      LinearMap.range (Fintype.linearCombination k b) = M := by
  constructor
  · rintro ⟨h1, h2⟩
    have hm : ∀ a : Fin m → k, ∑ j, a j • b j ∈ M := fun a =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h1 i)
    refine ⟨fun a a' h => (h2 _ (hm a)).unique rfl h, le_antisymm ?_ fun n hn => ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact hm a
    · obtain ⟨a, ha, -⟩ := h2 n hn
      exact ⟨a, ha.symm⟩
  · rintro ⟨h1, rfl⟩
    refine ⟨fun i => ⟨Pi.single i 1, by simp⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl, fun a' h => (h1 h).symm⟩

theorem IsBas.transfer {M : Submodule k N} {M' : Submodule k N'} {b b' : Fin m → N} {c : Fin m → N'}
    (A : Fin m → Fin m → k) (hb' : IsBas M b') (hA : ∀ i, b' i = ∑ j, A i j • b j) (hc : IsBas M' c) :
    IsBas M' fun i => ∑ j, A i j • c j := by
  let L : (Fin m → k) →ₗ[k] (Fin m → k) := Fintype.linearCombination k A
  have key : ∀ {P : Type} [AddCommGroup P] [Module k P] (d : Fin m → P),
      Fintype.linearCombination k (fun i => ∑ j, A i j • d j) = Fintype.linearCombination k d ∘ₗ L := by
    intro P _ _ d
    refine LinearMap.ext fun a => ?_
    simp only [L, LinearMap.comp_apply, Fintype.linearCombination_apply, Finset.smul_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  obtain rfl : b' = fun i => ∑ j, A i j • b j := funext hA
  rw [isBas_iff, key] at hb' ⊢
  rw [isBas_iff] at hc
  have hL : Function.Injective L := Function.Injective.of_comp (f := Fintype.linearCombination k b) hb'.1
  have hS : Function.Surjective L := LinearMap.surjective_of_injective hL
  exact ⟨hc.1.comp hL, by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hS), hc.2]⟩

def head (r : ℕ) (d : Fin m → N) : Submodule k N :=
  Submodule.span k (Set.range fun j : {j : Fin m // (j : ℕ) < r} => d j)

theorem mem_head {r : ℕ} {d : Fin m → N} {w : N} :
    w ∈ (head r d : Submodule k N) ↔ ∃ cf : Fin m → k, (∀ j : Fin m, r ≤ (j : ℕ) → cf j = 0) ∧ w = ∑ j, cf j • d j := by
  classical
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 h
    refine ⟨fun j => if h : (j : ℕ) < r then a ⟨j, h⟩ else 0, fun j hj => dif_neg (not_lt.2 hj), ?_⟩
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin m => (j : ℕ) < r)]
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun j : {j : Fin m // ¬ (j : ℕ) < r} => _)
      (fun j _ => by simp only [dif_neg j.2, zero_smul]), add_zero]
    exact Finset.sum_congr rfl fun j _ => by simp only [dif_pos j.2]
  · rintro ⟨cf, h0, rfl⟩
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < r
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rw [h0 j (not_lt.1 hj), zero_smul]
      exact zero_mem _

theorem head_le_iff {r : ℕ} {d d' : Fin m → N} :
    (head r d' : Submodule k N) ≤ head r d ↔ ∀ i : Fin m, (i : ℕ) < r → d' i ∈ (head r d : Submodule k N) := by
  rw [head, Submodule.span_le, Set.range_subset_iff]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

theorem head_ge {M : Submodule k N} {r : ℕ} {d b : Fin m → N} (hb : IsBas M b)
    (h : (head r b : Submodule k N) ≤ head r d) : (head r d : Submodule k N) ≤ head r b := by
  have hl : LinearIndependent k b := Fintype.linearIndependent_iff.2 fun g hg =>
    congrFun (((isBas_iff M b).1 hb).1 (a₁ := g) (a₂ := 0) (hg.trans (map_zero _).symm))
  have hl' : LinearIndependent k fun j : {j : Fin m // (j : ℕ) < r} => b j := hl.comp _ Subtype.val_injective
  have : FiniteDimensional k (head r d : Submodule k N) := FiniteDimensional.span_of_finite k (Set.finite_range _)
  refine (Submodule.eq_of_le_of_finrank_le h ?_).ge
  exact (finrank_range_le_card (R := k) _).trans (finrank_span_eq_card hl').ge

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Tan

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    {a : Fin m → S} {w w' : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) (h' : IsCombAtG t x v a w') :
    w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  obtain rfl : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rfl

theorem comb_push {τ : X' ⟶ X} (mu : SABMap t' t τ) {S : Type} [CommRing S] {x : Sp S ⟶ X'} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t'.G.left)} {a : Fin m → S} {w : Sp (DualNumber S) ⟶ t'.G.left}
    (h : IsCombAtG t' x v a w) : IsCombAtG t (x ≫ τ) (fun i => v i ≫ mu.φ) a (w ≫ mu.φ) := by
  obtain ⟨u, hu, rfl⟩ := h
  let U : tEpsG (x ≫ τ) ⟶ Over.mk ((tEpsG x).hom ≫ τ) := Over.homMk (𝟙 _) (by simp)
  let P : (tEpsG x ⟶ t'.G) →* (tEpsG (x ≫ τ) ⟶ t.G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U).comp (pushHom mu.cart (tEpsG x))
  have hP : ∀ z, (P z).left = z.left ≫ mu.φ := fun z => Category.id_comp _
  refine ⟨fun i => P (u i), fun i => by rw [hP, hu, Category.assoc], ?_⟩
  rw [← hP, map_list_prod, List.map_ofFn]
  rfl

theorem sameFlag_push {τ : X' ⟶ X} (mu : SABMap t' t τ) {S : Type} [CommRing S] {x : Sp S ⟶ X'}
    {ty ty' : (E →+* ℂ) → Finset ℕ} (hty : ∀ σ, ty σ ⊆ ty' σ) {u v : Vecs Dw t' S} (h : SameFlag ty' t' x u v) :
    SameFlag ty t (x ≫ τ) (Dw := Dw) (fun σ i => u σ i ≫ mu.φ) (fun σ i => v σ i ≫ mu.φ) := fun σ r hr i hi => by
  obtain ⟨cf, h0, hc⟩ := h σ r (hty σ hr) i hi
  exact ⟨cf, h0, comb_push mu hc⟩

variable {k : Type} [Field k] {x : Sp k ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback x).obj t.G}

theorem exists_coord (hx : IsUnivChart _ n xc) (u : Vecs Dw t k) (hu : ∀ σ i, IsTanAtG t x (u σ i)) :
    ∃ b : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → k, u = fun σ i => vec t x xc (b σ i) := by
  choose b hb using fun σ i => vec_exists hx (u σ i) (hu σ i)
  exact ⟨b, funext fun σ => funext fun i => hb σ i⟩

theorem isFrame_iff (hx : IsUnivChart _ n xc) {l : Level H} {c : Coeff l} (f : c.F →+* k)
    (b : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → k) :
    IsFrame t f x (Dw := Dw) (fun σ i => vec t x xc (b σ i)) ↔ ∀ σ, IsBas (eig c f hx σ) (b σ) := by
  constructor
  · rintro ⟨h1, h2⟩ σ
    refine ⟨fun i => (vec_eig_iff hx _ _).1 (h1 σ i).2, fun cc hc => ?_⟩
    simpa only [comb_iff hx] using h2 σ _ (vec_tan hx cc) ((vec_eig_iff hx _ _).2 hc)
  · intro h
    refine ⟨fun σ i => ⟨vec_tan hx _, (vec_eig_iff hx _ _).2 ((h σ).1 i)⟩, fun σ w hw he => ?_⟩
    obtain ⟨cc, rfl⟩ := vec_exists hx w hw
    simpa only [comb_iff hx] using (h σ).2 cc ((vec_eig_iff hx _ _).1 he)

theorem sameFlag_iff (hx : IsUnivChart _ n xc) (ty : (E →+* ℂ) → Finset ℕ)
    (b b' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → k) :
    SameFlag ty t x (Dw := Dw) (fun σ i => vec t x xc (b σ i)) (fun σ i => vec t x xc (b' σ i)) ↔
      ∀ σ, ∀ r ∈ ty σ, (head r (b' σ) : Submodule k _) ≤ head r (b σ) := by
  simp only [SameFlag, head_le_iff, mem_head, comb_iff hx]

theorem sameFlag_trans {ty : (E →+* ℂ) → Finset ℕ} {u v w : Vecs Dw t k} (hu : ∀ σ i, IsTanAtG t x (u σ i))
    (hv : ∀ σ i, IsTanAtG t x (v σ i)) (hw : ∀ σ i, IsTanAtG t x (w σ i)) (h : SameFlag ty t x u v)
    (h' : SameFlag ty t x v w) : SameFlag ty t x u w := by
  obtain ⟨n, xc, hx⟩ := exists_chart t x
  obtain ⟨a, rfl⟩ := exists_coord hx u hu
  obtain ⟨b, rfl⟩ := exists_coord hx v hv
  obtain ⟨c, rfl⟩ := exists_coord hx w hw
  rw [sameFlag_iff hx] at h h' ⊢
  exact fun σ r hr => (h' σ r hr).trans (h σ r hr)

theorem sameFlag_symm {ty : (E →+* ℂ) → Finset ℕ} {l : Level H} {c : Coeff l} {f : c.F →+* k} {u v : Vecs Dw t k}
    (hu : ∀ σ i, IsTanAtG t x (u σ i)) (hv : IsFrame t f x v) (h : SameFlag ty t x u v) : SameFlag ty t x v u := by
  obtain ⟨n, xc, hx⟩ := exists_chart t x
  obtain ⟨a, rfl⟩ := exists_coord hx u hu
  obtain ⟨b, rfl⟩ := exists_coord hx v fun σ i => (hv.1 σ i).1
  rw [sameFlag_iff hx] at h ⊢
  rw [isFrame_iff hx] at hv
  exact fun σ r hr => head_ge (hv σ) (h σ r hr)

theorem isFrame_push {τ : X' ⟶ X} (mu : SABMap t' t τ) {x' : Sp k ⟶ X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}
    {f : c.F →+* k} {f' : c'.F →+* k} {u v : Vecs Dw t' k} (hu : IsFrame t' f' x' u) (hv : IsFrame t' f' x' v)
    (h : IsFrame t f (x' ≫ τ) (Dw := Dw) fun σ i => u σ i ≫ mu.φ) :
    IsFrame t f (x' ≫ τ) (Dw := Dw) fun σ i => v σ i ≫ mu.φ := by
  choose A hA using fun σ i => (hu.2 σ (v σ i) (hv.1 σ i).1 (hv.1 σ i).2).exists
  have hA' := fun σ i => comb_push mu (hA σ i)
  obtain ⟨n, xc, hx⟩ := exists_chart t (x' ≫ τ)
  obtain ⟨n', xc', hx'⟩ := exists_chart t' x'
  obtain ⟨d, hd⟩ := exists_coord hx _ fun σ i => (h.1 σ i).1
  obtain ⟨a, rfl⟩ := exists_coord hx' u fun σ i => (hu.1 σ i).1
  obtain ⟨b, rfl⟩ := exists_coord hx' v fun σ i => (hv.1 σ i).1
  rw [hd, isFrame_iff hx] at h
  rw [isFrame_iff hx'] at hv
  have e : (fun σ i => vec t' x' xc' (b σ i) ≫ mu.φ : Vecs Dw t k) =
      fun σ i => vec t (x' ≫ τ) xc (∑ j, A σ i j • d σ j) := funext fun σ => funext fun i => by
    refine comb_unique (hA' σ i) ?_
    rw [show (fun j => vec t' x' xc' (a σ j) ≫ mu.φ) = fun j => vec t (x' ≫ τ) xc (d σ j) from congrFun hd σ]
    exact (comb_iff hx _ _ _).2 rfl
  rw [e, isFrame_iff hx]
  exact fun σ => IsBas.transfer (A σ) (hv σ) (fun i => (comb_iff hx' _ _ _).1 (hA σ i)) (h σ)

end Tan

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem ringHom_ext_valuationSubring {F k : Type} [Field F] [Field k] (V : ValuationSubring F) {f g : F →+* k}
    (h : f.comp V.subtype = g.comp V.subtype) : f = g := RingHom.ext fun x => by
  rcases V.mem_or_inv_mem x with hx | hx
  · exact RingHom.congr_fun h ⟨x, hx⟩
  · have : f x⁻¹ = g x⁻¹ := RingHom.congr_fun h ⟨x⁻¹, hx⟩
    rwa [map_inv₀, map_inv₀, inv_inj] at this

theorem pow_left_comp {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁] [GrpObj G₂]
    {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁)
    (h₂ : IsGrpPullback G₂ G f₂ φ₂) {T₁ : Over S₁} {T₂ : Over S₂} (x₁ : T₁ ⟶ G₁) (x₂ : T₂ ⟶ G₂) (r : T₂.left ⟶ T₁.left)
    (h : x₂.left ≫ φ₂ = r ≫ x₁.left ≫ φ₁) (n : ℕ) : (x₂ ^ n).left ≫ φ₂ = r ≫ (x₁ ^ n).left ≫ φ₁ := by
  let U : Over.mk (T₂.hom ≫ f₂) ⟶ Over.mk (T₁.hom ≫ f₁) := Over.homMk r (by
    have := congrArg (· ≫ G.hom) h
    simp only [Category.assoc, h₁.1.w, h₂.1.w, Over.w_assoc] at this
    exact this.symm)
  have e : pushHom h₂ T₂ x₂ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U (pushHom h₁ T₁ x₁) := Over.OverMorphism.ext h
  have e' : pushHom h₂ T₂ (x₂ ^ n) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U (pushHom h₁ T₁ (x₁ ^ n)) := by
    rw [map_pow, map_pow, map_pow, e]
  exact congrArg (fun q => q.left) e'

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isTrans_comp {i i₁ i₂ : Idx H p} {τ₁ : (Y i₁).X ⟶ (Y i).X} {τ₂ : (Y i₂).X ⟶ (Y i₁).X}
    {mu₁ : SABMap (Y i₁).t (Y i).t τ₁} {mu₂ : SABMap (Y i₂).t (Y i₁).t τ₂} (d₁ : i.l.Dvd i₁.l) (d₂ : i₁.l.Dvd i₂.l)
    (h₁ : IsTrans i i₁ τ₁ mu₁) (h₂ : IsTrans i₁ i₂ τ₂ mu₂) (mu : SABMap (Y i₂).t (Y i).t (τ₂ ≫ τ₁))
    (hmu : mu.φ = mu₂.φ ≫ mu₁.φ) : IsTrans i i₂ (τ₂ ≫ τ₁) mu := by
  obtain ⟨b₁, π₁, r₁, hb₁, hf₁, hs₁, fin₁, hj₁, he₁, hA₁⟩ := h₁
  obtain ⟨b₂, π₂, r₂, hb₂, hf₂, hs₂, fin₂, hj₂, he₂, hA₂⟩ := h₂
  have w₁ : τ₁ ≫ (Y i).s = (Y i₁).s ≫ spMap b₁ := by
    rw [← hf₁, ← hs₁, Category.assoc, Category.assoc, pullback.condition]
  let q : pullback (Y i₁).s (spMap b₂) ⟶ pullback (Y i).s (spMap (b₂.comp b₁)) :=
    pullback.lift (pullback.fst _ _ ≫ τ₁) (pullback.snd _ _) (by
      rw [Category.assoc, w₁, pullback.condition_assoc, sp_comp])
  let ρ : pullback (Y i).s (spMap (b₂.comp b₁)) ⟶ pullback (Y i).s (spMap b₁) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap b₂) (by
      rw [Category.assoc, sp_comp, pullback.condition])
  have hρ : IsPullback ρ (pullback.snd _ _) (pullback.snd _ _) (spMap b₂) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback (Y i).s (spMap b₁))
    rw [pullback.lift_fst, sp_comp]
    exact IsPullback.of_hasPullback _ _
  have hq : IsPullback (pullback.fst (Y i₁).s (spMap b₂)) q π₁ ρ := by
    refine IsPullback.of_bot ?_ ?_ hρ
    · rw [pullback.lift_snd, hs₁]
      exact IsPullback.of_hasPullback _ _
    · apply pullback.hom_ext
      · simp only [Category.assoc, hf₁, q, ρ, pullback.lift_fst]
      · simp only [Category.assoc, hs₁, q, ρ, pullback.lift_snd, pullback.lift_snd_assoc, pullback.condition]
  have finq : IsFinite q := MorphismProperty.of_isPullback hq fin₁
  have pw : ∀ {a a₁ a₂ : ℕ}, a ∣ a₁ → a₁ ∣ a₂ → ∀ (e : 𝟙_ (Over _) ⟶ (Y i).oF.t.G) (e₁ : 𝟙_ (Over _) ⟶ (Y i₁).oF.t.G)
      (e₂ : 𝟙_ (Over _) ⟶ (Y i₂).oF.t.G),
      (e₁ ^ (a₁ / a)).left ≫ (Y i₁).m.φ ≫ mu₁.φ = r₁ ≫ e.left ≫ (Y i).m.φ →
      (e₂ ^ (a₂ / a₁)).left ≫ (Y i₂).m.φ ≫ mu₂.φ = r₂ ≫ e₁.left ≫ (Y i₁).m.φ →
      (e₂ ^ (a₂ / a)).left ≫ (Y i₂).m.φ ≫ mu.φ = (r₂ ≫ r₁) ≫ e.left ≫ (Y i).m.φ := by
    intro a a₁ a₂ da da₁ e e₁ e₂ k₁ k₂
    have k := pow_left_comp (Y i₁).m.cart ((Y i₂).m.cart.comp mu₂.cart) e₁ (e₂ ^ (a₂ / a₁)) r₂ k₂ (a₁ / a)
    rw [← pow_mul, Nat.div_mul_div da₁ da] at k
    rw [hmu, Category.assoc, ← k₁]
    simpa only [Category.assoc] using congrArg (· ≫ mu₁.φ) k
  refine ⟨b₂.comp b₁, π₂ ≫ q, r₂ ≫ r₁, fun x => (hb₂ _).trans (hb₁ x), ?_, ?_, inferInstance, ?_,
    fun a => pw d₁.1 d₂.1 _ _ _ (he₁ a) (he₂ a), fun a => pw d₁.2.2 d₂.2.2 _ _ _ (hA₁ a) (hA₂ a)⟩
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hf₂]
  · rw [Category.assoc, pullback.lift_snd, hs₂]
  · rw [← Category.assoc, hj₂, Category.assoc, hj₁, Category.assoc]

theorem corr_refl (Z : Mdl Y i₀) : LocM.Corr Z Z := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ => subset_rfl⟩

theorem corr_trans {Z₁ Z₂ Z₃ : Mdl Y i₀} (h : LocM.Corr Z₁ Z₂) (h' : LocM.Corr Z₂ Z₃) : LocM.Corr Z₁ Z₃ :=
  ⟨⟨h'.1.1.trans h.1.1, h.1.2.1.trans h'.1.2.1, h'.1.2.2.trans h.1.2.2⟩, h'.2.1.trans h.2.1,
    fun σ => (h'.2.2 σ).trans (h.2.2 σ)⟩

theorem tan_chart (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m} {φ : Γ(Z.X, (Z.U a).1) →+* k}
    (h : spMap φ ≫ Z.chart a = w) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    IsTanAtG (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ σ j) := by
  rw [← h, Category.assoc]
  exact GlobalTheory.FactorDepth.isTanAtG_map _ φ ((Z.frame a).1 σ j).1

theorem range_subset_opn (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k}
    (h : Z.FlagAt w u) : Set.range w ⊆ Z.opn := by
  obtain ⟨a, φ, rfl, -⟩ := h
  rintro _ ⟨y, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, (Z.U a).2.range_fromSpec.le ⟨spMap φ y, (Scheme.Hom.comp_apply _ _ _).symm⟩⟩

theorem flagAt_two (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {u v : Vecs Dw (Y Z.i).t k}
    (hu : Z.FlagAt w u) (hv : Z.FlagAt w v) : ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (w ≫ Z.π) u ∧
      IsFrame (Y Z.i).t f (w ≫ Z.π) v ∧ SameFlag Z.ty (Y Z.i).t (w ≫ Z.π) u v := by
  obtain ⟨a, φ, ha, fu, su⟩ := hu
  obtain ⟨b, ψ, hb, fv, sv⟩ := hv
  have e : φ.comp (Z.alg a) = ψ.comp (Z.alg b) := ringHom_ext_valuationSubring (Z.i.c.V W) (spMap_inj (by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← sp_comp _ φ, ← sp_comp _ ψ, ← Z.alg_s, ← Z.alg_s, ← Category.assoc,
      ← Category.assoc, ha, hb]))
  have g := Z.glue k a b φ ψ (ha.trans hb.symm)
  rw [← Category.assoc, ha] at g
  refine ⟨_, fu, e ▸ fv, ?_⟩
  exact sameFlag_trans (fun σ j => (fu.1 σ j).1) (tan_chart Z ha) (fun σ j => (fv.1 σ j).1)
    (sameFlag_symm (tan_chart Z ha) fu su)
    (sameFlag_trans (tan_chart Z ha) (tan_chart Z hb) (fun σ j => (fv.1 σ j).1) g sv)

theorem isMap_comp {Z₁ Z₂ Z₃ : Mdl Y i₀} {f : Z₁.X ⟶ Z₂.X} {g : Z₂.X ⟶ Z₃.X} (hf : IsMap Z₁ Z₂ f) (hg : IsMap Z₂ Z₃ g) :
    IsMap Z₁ Z₃ (f ≫ g) := by
  refine ⟨corr_trans hf.1 hg.1, fun k _ w hw => ?_⟩
  obtain ⟨τ₁, mu₁, u, t₁, e₁, fu, fu'⟩ := hf.2 k w hw
  obtain ⟨τ₂, mu₂, v, t₂, e₂, fv, b, ψ, hb, fv', sv'⟩ := hg.2 k (w ≫ f) (range_subset_opn Z₂ fu')
  obtain ⟨mu, hmu⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₂ mu₁
  obtain ⟨c, k₁, k₂, k₃⟩ := flagAt_two Z₂ fv fu'
  have ex : ((w ≫ f) ≫ g) ≫ Z₃.π = ((w ≫ f) ≫ Z₂.π) ≫ τ₂ := e₂.trans (Category.assoc _ _ _).symm
  have fr : IsFrame (Y Z₃.i).t (ψ.comp (Z₃.alg b)) (((w ≫ f) ≫ g) ≫ Z₃.π) (Dw := Dw)
      fun σ j => (u σ j ≫ mu₁.φ) ≫ mu₂.φ := by
    rw [ex] at fv' ⊢
    exact isFrame_push mu₂ k₁ k₂ fv'
  have sf := sameFlag_push mu₂ hg.1.2.2 k₃
  rw [← ex] at sf
  refine ⟨τ₁ ≫ τ₂, mu, u, isTrans_comp hg.1.1 hf.1.1 t₂ t₁ mu hmu, ?_, fu, ?_⟩
  · rw [← Category.assoc w f g, ex, e₁]
    simp only [Category.assoc]
  · rw [hmu, ← Category.assoc w f g]
    simp only [← Category.assoc (u _ _)]
    exact ⟨b, ψ, hb, fr, sameFlag_trans (tan_chart Z₃ hb) (fun σ j => (fv'.1 σ j).1) (fun σ j => (fr.1 σ j).1) sv' sf⟩

theorem exists_dominating (hd : ∀ Z₁ Z₂ : Mdl Y i₀, LocM.Corr Z₁ Z₂ → ∃ Z', IsDiag Z₁ Z₂ Z') (n : ℕ)
    (Z : Fin (n + 1) → Mdl Y i₀) (hZ : ∀ a, (Z a).i = (Z 0).i ∧ (Z a).ty = (Z 0).ty) :
    ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧ ∀ a, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f := by
  classical
  have key : ∀ s : Finset (Fin (n + 1)), ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧
      ∀ a ∈ s, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨Z 0, rfl, rfl, by simp⟩
    | insert b s _ ih =>
      obtain ⟨Z', hi, ht, hm⟩ := ih
      have hc : LocM.Corr Z' (Z b) := by
        unfold LocM.Corr
        rw [hi, ht, (hZ b).1, (hZ b).2]
        exact corr_refl (Z 0)
      obtain ⟨Z'', hi', ht', f₁, f₂, m₁, m₂, -⟩ := hd Z' (Z b) hc
      refine ⟨Z'', hi'.trans hi, ht'.trans ht, fun a ha => ?_⟩
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨f₂, m₂⟩
      · obtain ⟨g, hg⟩ := hm a ha
        exact ⟨f₁ ≫ g, isMap_comp m₁ hg⟩
  obtain ⟨Z', hi, ht, hm⟩ := key Finset.univ
  exact ⟨Z', hi, ht, fun a => hm a (Finset.mem_univ a)⟩

end GlobalTheory.LocM.MapComp
