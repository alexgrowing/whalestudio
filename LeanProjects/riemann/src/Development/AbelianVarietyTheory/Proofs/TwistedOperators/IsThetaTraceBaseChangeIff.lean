import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.ThetaTraceBC

theorem gs_inj_of_flat {X Z : Scheme.{0}} (r : Z ⟶ X) [Flat r] (z : Z) (U : X.Opens) (h : r z ∈ U) {a b : Γ(X, U)}
    (e : gs r z U a = gs r z U b) : gs (𝟙 X) (r z) U a = gs (𝟙 X) (r z) U b := by
  rw [gs_stalkMap r z U h, gs_stalkMap r z U h] at e
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Z.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (r z)) (Z.presheaf.stalk z) e

theorem reps_iff {G G' : Type} [Group G] [Group G'] (u : G →* G') (hu : Function.Injective u) {C : Subgroup G}
    {C' : Subgroup G'} (h₁ : ∀ c, u c ∈ C' ↔ c ∈ C) (h₂ : ∀ c' ∈ C', ∃ c, u c = c') (p : ℕ) {n : ℕ} (r : Fin n → G) :
    IsRepsModTors C' p (fun i => u (r i)) ↔ IsRepsModTors C p r := by
  have e : ∀ a b : G, (u a * (u b)⁻¹) ^ p = 1 ↔ (a * b⁻¹) ^ p = 1 := fun a b => by
    rw [← map_inv, ← map_mul, ← map_pow, map_eq_one_iff u hu]
  refine and_congr (forall_congr' fun i => h₁ _) ⟨fun h c hc => ?_, fun h c' hc' => ?_⟩
  · simpa only [e] using h (u c) ((h₁ c).2 hc)
  · obtain ⟨c, rfl⟩ := h₂ c' hc'
    simpa only [e] using h c ((h₁ c).1 hc')

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A}

omit [GrpObj A] in

theorem isPullback_whisk {T T' : Over S} (σ : T' ⟶ T) :
    IsPullback (σ ▷ A).left (fst T' A).left (fst T A).left σ.left := by
  refine IsPullback.of_right (h₁₂ := (snd T A).left) (v₁₃ := A.hom) (h₂₂ := T.hom) ?_ ?_
    (IsPullback.of_hasPullback T.hom A.hom).flip
  · rw [← Over.comp_left, whiskerRight_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

theorem sv_of_pullRel {a : ℤ} {T T' : Over S} {σ : T' ⟶ T} {s : LB.Sec (LPow A L.L a T)}
    {s' : LB.Sec (LPow A L.L a T')} (h : PullRel L.L a (σ ▷ A) s s') {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z)
    {J} (hJ : Good L.L z J) : sv A L s' r z J = sv A L s (r ≫ (σ ▷ A).left) z J := by
  have e : (σ ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  refine Eq.trans ?_ (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s _ z J
    (fun _ => J (r ≫ (snd T' A).left)) (fun _ => by rw [Category.assoc, e])).symm
  exact h r z _ (hJ.mem (fun _ : Fin 1 => (snd T' A).left) r)

theorem sum_of_sv_flat {k : ℤ} {T : Over S} {n : ℕ} {a : LB.Sec (LPow A L.L k T)} {F : Fin n → LB.Sec (LPow A L.L k T)}
    {Z : Scheme.{0}} (π : Z ⟶ (T ⊗ A).left) [Flat π] [Surjective π]
    (h : ∀ z J, Good L.L z J → sv A L a π z J = ∑ i, sv A L (F i) π z J) (j) :
    a.f j = ∑ i, (F i).f j := by
  let b : LB.Sec (LPow A L.L k T) := SecM.toSec A (∑ i, SecM.ofSec A (F i))
  have hb : ∀ j, b.f j = ∑ i, (F i).f j := fun j => by
    show (∑ i, SecM.ofSec A (F i) : SecM A L.L k T).1 j = _
    rw [Submodule.coe_sum, Finset.sum_apply]; rfl
  rw [← hb]
  refine fn_ext fun y hy => ?_
  obtain ⟨z, rfl⟩ := π.surjective y
  obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (fun _ : Fin 1 => π ≫ (snd T A).left) j
    (fun a b _ => congrArg j (Subsingleton.elim _ _)) (fun a => Set.mem_iInter.1 hy a)
  refine gs_inj_of_flat π z _ hy ?_
  exact (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) a π z J j e).symm.trans
    (((h z J hJ).trans (sv_sum hb _ z hJ).symm).trans
      (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) b π z J j e))

theorem isMulPull_pull {N : ℕ} {T T' : Over S} (σ : T' ⟶ T) {s : LB.Sec (LPow A L.L 1 T)}
    {s' : LB.Sec (LPow A L.L 1 T')} {s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)} (hs : PullRel L.L 1 (σ ▷ A) s s')
    (h : IsMulPull A L N s s₁) : ∃ s₁', IsMulPull A L N s' s₁' ∧ PullRel L.L _ (σ ▷ A) s₁ s₁' := by
  obtain ⟨α₀, α, g₀, n₀, cα, tw⟩ := h
  have e1 : (σ ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whisk_snd]
  have e2 : (σ ▷ A).left ≫ (snd T A ^ N).left = (snd T' A ^ N).left := by
    rw [← Over.comp_left, MonObj.comp_pow, whisk_snd]
  have eα : ∀ kk, (![(snd T' A).left, (snd T' A ^ N).left] : Fin 2 → _) kk =
      (σ ▷ A).left ≫ (![(snd T A).left, (snd T A ^ N).left] : Fin 2 → _) kk := by
    intro kk; fin_cases kk
    · exact e1.symm
    · exact e2.symm
  obtain ⟨α', -, hα'⟩ := exists_gen_pull (L := L.L) _ _ α (σ ▷ A).left _ eα
  obtain ⟨s₁', hs₁'⟩ := exists_pullRel L.L ((N : ℤ) ^ 2) (σ ▷ A) (whiskerRight_snd σ A) s₁
  refine ⟨s₁', ⟨α₀, α', g₀, n₀, ?_, ?_⟩, hs₁'⟩
  · refine corr_of_val L.isLB fun y J hJ => ?_
    rw [val_of_pull eα hα' _ y hJ, val_corr hJ cα, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, e1]
  · exact twist_pull (σ ▷ A) (whiskerRight_snd σ A) (mul_whisk σ N) hα' hs hs₁' tw

variable {Y Y' : Scheme.{0}} {x x' : Y ⟶ S} {w w' : Y' ⟶ S} {σ : Over.mk w ⟶ Over.mk x} {σ' : Over.mk w' ⟶ Over.mk x'}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {Ψ' : (Over.mk w ⊗ A).left ⟶ (Over.mk w' ⊗ A).left}

omit [GrpObj A] in
theorem snd_comm (hΨ : Ψ' ≫ (σ' ▷ A).left = (σ ▷ A).left ≫ Ψ) :
    Ψ' ≫ (snd (Over.mk w') A).left = (σ ▷ A).left ≫ Ψ ≫ (snd (Over.mk x') A).left := by
  rw [← Category.assoc, ← hΨ, Category.assoc, ← Over.comp_left, whiskerRight_snd]

theorem origin_whisk {T T' : Over S} (σ : T' ⟶ T) :
    (ptSecT A (1 : T' ⟶ A)).left ≫ (σ ▷ A).left = σ.left ≫ (ptSecT A (1 : T ⟶ A)).left := by
  rw [← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT, lift_whiskerRight, comp_lift, MonObj.comp_one,
    Category.id_comp, Category.comp_id]

theorem isRigIso_pull {k : ℤ} (hσ : (σ'.left : Y' ⟶ Y) = σ.left) (hΨ : Ψ' ≫ (σ' ▷ A).left = (σ ▷ A).left ≫ Ψ)
    (h0 : Ψ' ≫ (fst (Over.mk w') A).left = (fst (Over.mk w) A).left) {β : LB.Gen (isoLB A L Ψ k)}
    (hβ : IsRigIso A L Ψ k β) : ∃ β', IsRigIso A L Ψ' k β' ∧ ∀ {Z : Scheme.{0}} (r : Z ⟶ (Over.mk w ⊗ A).left) (z : Z)
      {J}, Good L.L z J → val β' r z J = val β (r ≫ (σ ▷ A).left) z J := by
  have e : ∀ i, isoφ A Ψ' i = (σ ▷ A).left ≫ isoφ A Ψ i := by
    intro i; fin_cases i
    · exact (by rw [← Over.comp_left, whiskerRight_snd] :
        (snd (Over.mk w) A).left = (σ ▷ A).left ≫ (snd (Over.mk x) A).left)
    · exact snd_comm hΨ
  obtain ⟨β', g, H⟩ := exists_gen_pull (L := L.L) _ ![k, -1] β (σ ▷ A).left _ e
  refine ⟨β', ⟨⟨h0, ?_⟩, g hβ.2.1, corr_of_val L.isLB fun z J hJ => ?_⟩, fun r z J hJ => val_of_pull e H r z hJ⟩
  · refine (isPullback_whisk σ').hom_ext ?_ ?_
    · rw [Category.assoc, hΨ, ← Category.assoc, origin_whisk, Category.assoc, hβ.1.2, origin_whisk, hσ]
    · rw [Category.assoc, h0, ptSecT, ptSecT, lift_l_fst, lift_l_fst]; rfl
  · have a := val_corr hJ hβ.2.2 (σ.left : Y' ⟶ Y)
    rw [val_pull hJ, val_mul hJ] at a
    refine (val_pull hJ _ _ _).trans ((val_of_pull e H _ z hJ).trans ?_)
    refine (congrArg (fun q => val β q z J) ((Category.assoc _ _ _).trans ((Category.id_comp _).trans
      (origin_whisk σ)))).trans (a.trans (Eq.trans ?_ (val_mul hJ _ _ _).symm))
    have w₁ : (σ.left : Y' ⟶ Y) ≫ x = 𝟙 Y' ≫ w := (Over.w σ).trans (Category.id_comp _).symm
    have w₂ : (σ.left : Y' ⟶ Y) ≫ x' = 𝟙 Y' ≫ w' := hσ ▸ (Over.w σ').trans (Category.id_comp _).symm
    refine congrArg₂ (· * ·) ((val_rigT (Over.mk x) _ _ z hJ).trans (Eq.trans ?_ (val_rigT (Over.mk w) _ _ z hJ).symm))
      ((val_rigT (Over.mk x') _ _ z hJ).trans (Eq.trans ?_ (val_rigT (Over.mk w') _ _ z hJ).symm))
    · exact congrArg (fun q => val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig q z J ^ k) w₁
    · exact congrArg (fun q => val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig q z J ^ (-1 : ℤ)) w₂

theorem transl_whisk_left {T T' : Over S} (σ : T' ⟶ T) (c : T ⟶ A) :
    (translT A (σ ≫ c)).left ≫ (σ ▷ A).left = (σ ▷ A).left ≫ (translT A c).left := by
  rw [← Over.comp_left, transl_whisk, Over.comp_left]

theorem mem_transKer_pull [Epi (σ ▷ A).left] (hΨ : Ψ' ≫ (σ' ▷ A).left = (σ ▷ A).left ≫ Ψ)
    (h0 : Ψ' ≫ (fst (Over.mk w') A).left = (fst (Over.mk w) A).left) (c : Over.mk x ⟶ A) :
    σ ≫ c ∈ transKer A Ψ' ↔ c ∈ transKer A Ψ := by
  rw [mem_transKer, mem_transKer, ← cancel_epi (σ ▷ A).left, ← Category.assoc, ← transl_whisk_left, Category.assoc,
    ← hΨ]
  refine ⟨fun h => by rw [← Category.assoc, h], fun h => (isPullback_whisk σ').hom_ext ?_ ?_⟩
  · rw [Category.assoc, h]
  · rw [Category.assoc, h0, translT, lift_l_fst]

theorem pow_eq_one_of_mem [IsCommMonObj A] (hΨ : Ψ' ≫ (σ' ▷ A).left = (σ ▷ A).left ≫ Ψ) {N : ℕ}
    {Φ : (Over.mk x' ⊗ A).left ⟶ (Over.mk x ⊗ A).left} (hΦ : Ψ ≫ Φ = (mulT A (Over.mk x) N).left)
    {c : Over.mk w ⟶ A} (hc : c ∈ transKer A Ψ') : c ^ N = 1 := by
  rw [← mem_transKer_mulT, mem_transKer]
  have e : (mulT A (Over.mk w) N).left ≫ (σ ▷ A).left = Ψ' ≫ (σ' ▷ A).left ≫ Φ := by
    rw [← Over.comp_left, mul_whisk, Over.comp_left, ← hΦ, ← Category.assoc, ← hΨ, Category.assoc]
  refine (isPullback_whisk σ).hom_ext ?_ ?_
  · rw [Category.assoc, e, ← Category.assoc, mem_transKer.1 hc]
  · rw [Category.assoc, mulT, lift_l_fst, translT, lift_l_fst]

def precomp {T T' : Over S} (σ : T' ⟶ T) : (T ⟶ A) →* (T' ⟶ A) :=
  MonoidHom.mk' (fun c => σ ≫ c) fun a b => MonObj.comp_mul σ a b

theorem isThetaTrace_iff_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) [Flat σ.left] [Surjective σ.left]
    (hσ : (σ'.left : Y' ⟶ Y) = σ.left) (hΨ : Ψ' ≫ (σ' ▷ A).left = (σ ▷ A).left ≫ Ψ)
    (h0 : Ψ' ≫ (fst (Over.mk w') A).left = (fst (Over.mk w) A).left)
    (hrat : ∀ c' ∈ transKer A Ψ', ∃ c : Over.mk x ⟶ A, σ ≫ c = c') {p : ℕ}
    {s : LB.Sec (LPow A L.L 1 (Over.mk x))} {s' : LB.Sec (LPow A L.L 1 (Over.mk x'))}
    {u : LB.Sec (LPow A L.L 1 (Over.mk w))} {u' : LB.Sec (LPow A L.L 1 (Over.mk w'))}
    (hu : PullRel L.L 1 (σ ▷ A) s u) (hu' : PullRel L.L 1 (σ' ▷ A) s' u')
    (hβ : ∃ β, IsRigIso A L Ψ ((p : ℤ) ^ 2) β) (hs : ∃ s₁, IsMulPull A L p s s₁) :
    IsThetaTrace A L Ψ p s s' ↔ IsThetaTrace A L Ψ' p u u' := by
  have : Flat (σ ▷ A).left := MorphismProperty.of_isPullback (P := @Flat) (isPullback_whisk σ).flip inferInstance
  have : Surjective (σ ▷ A).left :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_whisk σ).flip inferInstance
  have := Flat.epi_of_flat_of_surjective (σ ▷ A).left
  have := Flat.epi_of_flat_of_surjective σ.left
  have hinj : Function.Injective (precomp (A := A) σ) := fun a b e =>
    Over.OverMorphism.ext ((cancel_epi σ.left).1 (congrArg (·.left) e))
  have hr := fun {n : ℕ} (r : Fin n → (Over.mk x ⟶ A)) =>
    reps_iff (precomp σ) hinj (mem_transKer_pull hΨ h0) hrat p r
  constructor
  · intro h
    obtain ⟨β, s₁, n, c, hβ, hs, hc, hv⟩ := isThetaTrace_iff.1 h
    obtain ⟨β', hβ', vβ⟩ := isRigIso_pull hσ hΨ h0 hβ
    obtain ⟨u₁, hu₁, v₁⟩ := isMulPull_pull σ hu hs
    refine isThetaTrace_iff.2 ⟨β', u₁, n, fun i => σ ≫ c i, hβ', hu₁, (hr c).2 hc, fun Z r z J hJ => ?_⟩
    rw [sv_of_pullRel hu' _ z hJ, Category.assoc, hΨ, ← Category.assoc, hv _ _ z J hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vβ _ z hJ, sv_of_pullRel v₁ _ z hJ, Category.assoc, Category.assoc, transl_whisk_left]
  · intro h
    obtain ⟨β'', u₂, n, c', hβ'', hu₂, hc', hv⟩ := isThetaTrace_iff.1 h
    obtain ⟨β, hβ⟩ := hβ
    obtain ⟨s₁, hs⟩ := hs
    obtain ⟨β', hβ', vβ⟩ := isRigIso_pull hσ hΨ h0 hβ
    obtain ⟨u₁, hu₁, v₁⟩ := isMulPull_pull σ hu hs
    obtain rfl := hu₂.unique hG hA hu₁
    choose c hc using fun i => hrat _ (hc'.1 i)
    obtain rfl : c' = fun i => σ ≫ c i := funext fun i => (hc i).symm
    have hc := (hr c).1 hc'
    obtain ⟨t, ht⟩ := exists_isCarried hβ.2.1 s'
    choose U hcU hU using fun i => exists_isDescLift hβ.2.1 (hc.1 i)
    choose F hF using fun i => exists_isActOf (U i) s₁
    obtain rfl : c = fun i => (U i).pt := funext fun i => (hcU i).symm
    refine ⟨β, s₁, t, n, U, F, hβ, hs, ht, hc, hU, hF, sum_of_sv_flat (σ ▷ A).left fun z J hJ => ?_⟩
    have e := hv _ (𝟙 _) z J hJ
    rw [sv_of_pullRel hu' _ z hJ, Category.id_comp, hΨ] at e
    rw [ht.val _ z hJ, e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_val (hF i) _ z hJ, (hU i).val _ z hJ, Units.val_mul, hβ''.val_unique hG hA hβ' _ z hJ, vβ _ z hJ,
      sv_of_pullRel v₁ _ z hJ, Category.id_comp, transl_whisk_left]
    ring

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem conj_comp_eq_mulT {K : Type} [CommRing K] {x x' : Sp K ⟶ Xo.X} {f : Fib Xo x ⟶ Fib Xo x'}
    {f' : Fib Xo x' ⟶ Fib Xo x} {n : ℕ} (h : f ≫ f' = 𝟙 _ ^ n) :
    conj x x' f.left ≫ conj x' x f'.left = (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G ^ n) = 𝟙 (Fib Xo x) ^ n := by
    have := map_pow (Over.pullback x).homMonoidHom (𝟙 Xo.univ.t.G) n
    rw [← (Over.pullback x).map_id]
    exact this
  have e₁ : conj x x (f ≫ f').left = conj x x' f.left ≫ conj x' x f'.left := by
    simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
    rw [Over.comp_left]
    simp only [Category.assoc]
  rw [← e₁, h, ← e, mulT, ← Category.comp_id (snd (Over.mk x) Xo.univ.t.G), ← MonObj.comp_pow]
  refine gx_ext ?_ ?_
  · rw [lift_l_fst]
    exact (over_iff _).2 (pullback.lift_snd _ _ _)
  · rw [lift_l_snd, conj_apply, Category.assoc, Category.assoc, swap_inv_snd, Over.comp_left, ← swap_hom_fst,
      Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem gs_appLE {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens} (le : V ≤ g ⁻¹ᵁ U)
    (h : r z ∈ V) (a : Γ(X, U)) : gs r z V ((g.appLE U V le).hom a) = gs (r ≫ g) z U a :=
  (gs_res r z le h _).trans (gs_pull r g z U (le h) a)

variable {c : Coeff l} {K L : Type} [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] {φ : K →ₐ[c.F] L}

def ptMap {y : FrPt Xo c K} {y' : FrPt Xo c L} (h : FrMap φ y y') : (Over.mk y'.x : Over Xo.X) ⟶ Over.mk y.x :=
  Over.homMk (spMap φ.toRingHom) h.1.symm

theorem pullRel_of_frMap {y : FrPt Xo c K} {y' : FrPt Xo c L} (h : FrMap φ y y') :
    PullRel Xo.univ.t.PP.L 1 (ptMap h ▷ Xo.univ.t.G) y.s y'.s := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := h.2.2
  obtain rfl : pm = (ptMap h ▷ Xo.univ.t.G).left := gx_ext
    (by rw [h₂, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [h₁, ← Over.comp_left, whiskerRight_snd])
  intro Z r z j hz
  have le := chart_le_res Xo.univ.t.G Xo.univ.t.PP.L (ptMap h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) 1 j
  exact (congrArg (gs r z _) (h₃ j le).symm).trans (gs_appLE r _ z le hz _)

theorem isThetaTrace_baseChange_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (y z : FrPt Xo c K) (y' z' : FrPt Xo c L) (f : Fib Xo y.x ⟶ Fib Xo z.x) (f' : Fib Xo z.x ⟶ Fib Xo y.x) (g : Fib Xo y'.x ⟶ Fib Xo z'.x) (p : ℕ), 0 < p → FrMap φ y y' → FrMap φ z z' → IsPair (p ^ 2) f f' → IsBC φ.toRingHom f g → AllRat Xo y.x (p ^ 2) → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) ((p : ℤ) ^ 2) β) → (IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y.x z.x f.left) p y.s z.s ↔ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj y'.x z'.x g.left) p y'.s z'.s) := by
  intro E _ _ _ H Dw l Xo c K L _ _ _ _ φ y z y' z' f f' g p _ hy hz hf hbc hrat hβ
  have : Flat (ptMap hy).left := by
    show Flat (spMap φ.toRingHom)
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have : Surjective (ptMap hy).left := ⟨fun q => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have hΨ : conj y'.x z'.x g.left ≫ (ptMap hz ▷ Xo.univ.t.G).left =
      (ptMap hy ▷ Xo.univ.t.G).left ≫ conj y.x z.x f.left := by
    have a : ∀ {v : FrPt Xo c K} {v' : FrPt Xo c L} (h : FrMap φ v v'),
        ((swap v'.x).inv ≫ (ptMap h ▷ Xo.univ.t.G).left ≫ (swap v.x).hom) ≫ pullback.fst _ _ = pullback.fst _ _ :=
      fun h => by
        rw [Category.assoc, Category.assoc, swap_hom_fst, ← Over.comp_left, whiskerRight_snd, swap_inv_snd]
    have b : ∀ {v : FrPt Xo c K} {v' : FrPt Xo c L} (h : FrMap φ v v'),
        ((swap v'.x).inv ≫ (ptMap h ▷ Xo.univ.t.G).left ≫ (swap v.x).hom) ≫ pullback.snd _ _ =
          pullback.snd _ _ ≫ spMap φ.toRingHom := fun h => by
      rw [Category.assoc, Category.assoc, swap_hom_snd, ← Over.comp_left, whiskerRight_fst, Over.comp_left,
        swap_inv_fst_assoc]
      rfl
    have e := hbc.2.2 _ _ (a hy) (b hy) (a hz) (b hz)
    rw [conj_apply, conj_apply, ← cancel_mono (swap z.x).hom, ← cancel_epi (swap y'.x).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using e
  refine isThetaTrace_iff_pull (A := Xo.univ.t.G) (L := Xo.univ.t.PP) abelianSchemeLaws_all.1.globalFns (UnivPol.pol Xo).isAb (σ := ptMap hy)
    (σ' := ptMap hz) rfl hΨ ((over_iff _).2 (Over.w g)) (fun c' hc' => ?_) (pullRel_of_frMap hy) (pullRel_of_frMap hz) hβ
    (exists_isMulPull p y.s)
  have hp := pow_eq_one_of_mem hΨ (conj_comp_eq_mulT hf.2.2.1) hc'
  let k : (Over.mk (spMap φ.toRingHom ≫ y.x) : Over Xo.X) ⟶ Over.mk y'.x := Over.homMk (𝟙 _) ((Category.id_comp _).trans hy.1)
  obtain ⟨a, ha⟩ := hrat L φ.toRingHom (k ≫ c') (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext (ha.symm.trans (Category.id_comp _))⟩

end GlobalTheory.ThetaTraceBC
