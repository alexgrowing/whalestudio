import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RegularUnitPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeChar0

section Weil

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommutatorPairing

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem exists_theta_one (hL : L.IsLB) (T : Over S) :
    ∃ θ : ThetaGrp A L k T, θ.pt = 1 ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L z J →
      thetaVal θ t a z J = 1 := by
  have e : (translPt A (1 : T ⟶ A)) = snd T A := by
    show (fst T A ≫ (1 : T ⟶ A)) * snd T A = snd T A
    rw [comp_one, _root_.one_mul]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K := PEmpty) (K' := Fin 2) (φ := PEmpty.elim) (ε := PEmpty.elim)
    (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ h => by
      rw [Fin.prod_univ_two, e]
      simp)
    (LB.oneGen L) (LB.isGen_oneGen L)
  exact ⟨⟨1, u, hu⟩, rfl, fun Z t a z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩

theorem weilIs_one_left (hL : L.IsLB) {T : Over S} {y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (H : WeilIs A L k 1 y c) : c = 1 := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hp, ⟨_, θy, _, hy⟩, hc⟩ := H p
  obtain ⟨θ, h1, hθ⟩ := exists_theta_one (k := k) (A := A) hL (overRes V)
  have hC := hc θ θy (by rw [h1, comp_one]) hy
  rw [commIsOf_iff hL] at hC
  let z : (overRes V).left := ⟨p, hp⟩
  choose J hJ using fun ψ : (overRes V).left ⟶ A.left => exists_chart hL (ψ z)
  have hJ' : Good L z J := hJ
  have h2 := hC (overRes V) (𝟙 _) 1 z J hJ'
  rw [commVal, hθ _ _ _ _ _ hJ', hθ _ _ _ _ _ hJ', h1, comp_one, _root_.one_mul, _root_.one_mul, _root_.mul_one,
    mul_inv_cancel] at h2
  have g : gm (V.ι) z ⊤ c = gm (V.ι) z ⊤ 1 := by
    rw [map_one]
    refine Eq.trans ?_ h2.symm
    exact ((gm_unitRes V c (𝟙 _) z).trans (by rw [Category.id_comp])).symm
  exact gm_inj V.ι z (U := ⊤) (U' := ⊤) (show V.ι z ∈ (⊤ : T.left.Opens) from trivial)
    (show V.ι z ∈ (⊤ : T.left.Opens) from trivial) g

end Weil

section Ring

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}

theorem unitAt_mul {a b : Ω} (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unitAt_natCast (h : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) (n : ℕ) (hn : n ≠ 0) : unitAt ξ q (n : Ω) :=
  _root_.UpperTheory.Reformulated.B.RegularUnitPoints.main h n hn

theorem inv_mem_regAt [CharZero Ω] (h : ∀ n : ℕ, n ≠ 0 → unitAt ξ q (n : Ω)) {x : Ω} (hx : x ∈ regAt ξ q)
    (hi : IsIntegral ℤ x) : x⁻¹ ∈ regAt ξ q := by
  let A : Subalgebra ℚ Ω :=
    { (regAt ξ q).toSubsemiring with
      algebraMap_mem' := fun r => by
        show algebraMap ℚ Ω r ∈ regAt ξ q
        rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
        exact mul_mem (intCast_mem _ _) (h _ r.den_nz).2.2 }
  exact Subalgebra.inv_mem_of_algebraic A (x := ⟨x, hx⟩) (hi.tower_top (A := ℚ)).isAlgebraic

end Ring

section Stable

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem lat_stable (M : LieModel G ξ E) {O : Type} [CommRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (ρ : O →+* Module.End Ω E) (h : M.IsActOf act.act ρ) (q : Cpt ξ) (a : O) {e : E} (he : e ∈ M.lat q) :
    ρ a e ∈ M.lat q := by
  obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
  refine (M.mem_lat_iff q _).2 ⟨v ≫ act.act a, ?_⟩
  rw [LieModel.extends_iff] at hv ⊢
  have := act.hom a
  refine ⟨?_, ?_⟩
  · have h1 := hv.1
    rw [LieTangent.isTanAt_iff] at h1 ⊢
    rw [← Category.assoc, h1, MonObj.one_comp]
  · rw [h a e, hv.2, Category.assoc]

end Stable

section Linear

variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {R : Subring Ω}

theorem mem_eigSp_apply {O : Type} [CommRing O] {ρ : O →+* Module.End Ω E} {σ : O →+* Ω} {e : E}
    (he : e ∈ eigSp ρ σ) (a : O) : ρ a e = σ a • e := by
  have := (Submodule.mem_iInf _).1 he a
  simpa [sub_eq_zero] using this

theorem mem_of_sum_mem (P : Submodule R E) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E) {I : Type}
    [DecidableEq I] (σ : I → (O →+* Ω)) (hst : ∀ a, ∀ e ∈ P, ρ a e ∈ P) (hreg : ∀ s a, σ s a ∈ R)
    (hsep : ∀ s t, s ≠ t → ∃ a, σ s a ≠ σ t a ∧ (σ s a - σ t a)⁻¹ ∈ R) (A : Finset I) :
    ∀ f : I → E, (∀ s ∈ A, f s ∈ eigSp ρ (σ s)) → (∑ s ∈ A, f s) ∈ P → ∀ s ∈ A, f s ∈ P := by
  have smul_mem' : ∀ (c : Ω), c ∈ R → ∀ e ∈ P, c • e ∈ P := fun c hc e he => P.smul_mem (⟨c, hc⟩ : R) he
  induction A using Finset.induction_on with
  | empty => simp
  | insert t A ht ih =>
    intro f hf hsum
    rw [Finset.sum_insert ht] at hsum
    have key : ∀ s ∈ A, f s ∈ P := by
      intro s hs
      have hne : s ≠ t := fun e => ht (e ▸ hs)
      obtain ⟨a, ha, hinv⟩ := hsep s t hne
      have hg : (∑ u ∈ A, (σ u a - σ t a) • f u) ∈ P := by
        have e : (∑ u ∈ A, (σ u a - σ t a) • f u) =
            ρ a (f t + ∑ u ∈ A, f u) - σ t a • (f t + ∑ u ∈ A, f u) := by
          rw [map_add, map_sum, mem_eigSp_apply (hf t (Finset.mem_insert_self _ _)) a, smul_add, Finset.smul_sum]
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [Finset.sum_congr rfl fun u hu =>
            (mem_eigSp_apply (hf u (Finset.mem_insert_of_mem hu)) a).symm]
          abel
        rw [e]
        exact P.sub_mem (hst a _ hsum) (smul_mem' _ (hreg t a) _ hsum)
      have h1 := ih (fun u => (σ u a - σ t a) • f u)
        (fun u hu => (eigSp ρ (σ u)).smul_mem _ (hf u (Finset.mem_insert_of_mem hu))) hg s hs
      have h2 := smul_mem' _ hinv _ h1
      simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 ha)] using h2
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · have := P.sub_mem hsum (P.sum_mem key)
      simpa using this
    · exact key s hs

theorem mem_iSup_of_dual {I : Type} [Fintype I] [DecidableEq I] (V : I → Submodule Ω E) (hind : iSupIndep V)
    (htop : ⨆ s, V s = ⊤) (r : I → ℕ) (b : ∀ s, Fin (r s) → E) (hli : ∀ s, LinearIndependent Ω (b s))
    (hsp : ∀ s, Submodule.span Ω (Set.range (b s)) = V s) (P : I → Submodule R E)
    (hP : ∀ s, P s = Submodule.span R (Set.range (b s))) (x : E)
    (hx : ∀ w : Module.Dual Ω E, (∀ s, ∀ e ∈ P s, w e ∈ R) → w x ∈ R) : x ∈ ⨆ s, P s := by
  have hint : DirectSum.IsInternal V := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let B : ∀ s, Module.Basis (Fin (r s)) Ω (V s) := fun s =>
    (Module.Basis.span (hli s)).map (LinearEquiv.ofEq _ _ (hsp s))
  let C := hint.collectedBasis B
  have hC : ∀ s i, C ⟨s, i⟩ = b s i := fun s i => by
    simp [C, B, DirectSum.IsInternal.collectedBasis_coe, Module.Basis.span_apply]
  have hcoord : ∀ j, C.repr x j ∈ R := by
    intro j
    refine hx (C.coord j) fun s e he => ?_
    rw [hP s] at he
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [← hC, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simpa using zero_mem R
    | add y z _ _ hy hz => simpa using add_mem hy hz
    | smul c y _ hy =>
      have : C.coord j (c • y) = (c : Ω) * C.coord j y := by
        show C.coord j ((c : Ω) • y) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem c.2 hy
  rw [← C.sum_repr x]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hm : C j ∈ P j.1 := by
    obtain ⟨s, i⟩ := j
    rw [hC, hP s]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact (⨆ s, P s).smul_mem (⟨_, hcoord j⟩ : R) (Submodule.mem_iSup_of_mem _ hm)

end Linear

section HT

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem htOm_eq_omLat (M : LieModel G ξ E) {L : LB G.left} (hL : L.IsLB) (n : ℕ) (q : Cpt ξ)
    (hn : unitAt ξ q (n : Ω)) : M.htOm L n q = M.omLat q := by
  refine le_antisymm (M.htOm_le L n q) fun w hw => Submodule.subset_span ⟨1, one_pow n, hw, ⊤, 1, trivial, ?_, ?_⟩
  · intro k _ _ i xk g c h hx _ hW
    have hx1 : xk = 1 := by
      refine Over.OverMorphism.ext (hx.trans ?_)
      exact congrArg (fun f => f.left)
        (comp_one (M := G) (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ))
    subst hx1
    have hc : unitOn c = 1 := weilIs_one_left hL hW
    have hc1 : c = 1 := by
      apply Units.ext
      have := congrArg Units.val hc
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1
      simpa [unitOn] using this
    rw [hc1]
    simp [secVal]
  · intro e v he h
    have hr : w e ∈ regAt ξ q :=
      (show ∀ e ∈ M.lat q, w e ∈ regAt ξ q from hw) e ((M.mem_lat_iff q e).2 ⟨v, he⟩)
    refine ⟨(n : Ω)⁻¹ * w e, mul_mem hn.2.2 hr, ?_⟩
    rw [mul_inv_cancel_left₀ hn.1]
    simp [secVal]

variable (M : LieModel G ξ E) {L : LB G.left} {n : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω) {q : Cpt ξ}

theorem htDual_eq_eigLat (hL : L.IsLB) (hn : unitAt ξ q (n : Ω))
    (hbi : ∀ x, (∀ w ∈ M.omLat q, w x ∈ regAt ξ q) → x ∈ M.lat q) :
    M.htDual L n ρ σ q = M.eigLat ρ σ q := by
  refine le_antisymm (fun e he => ?_) (M.eigLat_le_htDual L n ρ σ q)
  rw [LieModel.mem_htDual_iff, htOm_eq_omLat M hL n q hn] at he
  exact ⟨hbi e he.2, he.1⟩

theorem htW_eq_eigLat (hd : M.htDual L n ρ σ q = M.eigLat ρ σ q) (hσ : ∀ d, σ d ∈ regAt ξ q) (𝔡 : Ideal O)
    (N : ℕ) (hN : (N : O) ∈ 𝔡) (hu : unitAt ξ q (N : Ω)) : M.htW L n ρ σ 𝔡 q = M.eigLat ρ σ q := by
  refine le_antisymm (Submodule.span_le.2 fun e he => ?_) fun e he => Submodule.subset_span ⟨he.2, fun d _ => ?_⟩
  · have h1 := he.2 _ hN
    rw [hd, map_natCast] at h1
    have h2 : (N : Ω)⁻¹ • (N : Ω) • e ∈ M.lat q := (M.lat q).smul_mem (⟨_, hu.2.2⟩ : regAt ξ q) h1.1
    rw [smul_smul, inv_mul_cancel₀ hu.1, one_smul] at h2
    exact ⟨h2, he.1⟩
  · rw [hd]
    exact (M.eigLat ρ σ q).smul_mem (⟨_, hσ d⟩ : regAt ξ q) he

end HT

theorem lattices_of_char_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), Function.Injective β → ∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → (∀ s, 𝔐.V s q = 𝔐.dR s q) ∧ (∀ p : ℕ, p.Prime → ∀ s, 𝔐.HT p s q = 𝔐.dR s q) ∧ 𝔐.M.lat q = ⨆ s, 𝔐.dR s q := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 hβ q hq
  classical
  obtain ⟨-, -, hchar, hinj, -, htop, hind, hreg⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
  haveI := hchar
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  have hnat := unitAt_natCast (q := q) hq
  have hV : ∀ s, 𝔐.V s q = 𝔐.dR s q := fun s =>
    Lat.patch_of_not S _ _ fun p hp => hq p (𝔐.S_prime p hp)
  have hint : ∀ (s : CMType H ⊕ CMType H) a, IsIntegral ℤ (𝔐.emb s a) := fun s a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom
  have hsep : ∀ s t, s ≠ t → ∃ a, 𝔐.emb s a ≠ 𝔐.emb t a ∧ (𝔐.emb s a - 𝔐.emb t a)⁻¹ ∈ regAt 𝔐.ξ q := by
    intro s t hst
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (fun e => hst (hinj e))
    exact ⟨a, ha, inv_mem_regAt hnat (sub_mem (hreg s a q) (hreg t a q)) ((hint s a).sub (hint t a))⟩
  have hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q := by
    refine le_antisymm (fun e he => ?_) (iSup_le fun s => inf_le_left)
    have he' : e ∈ ⨆ s, 𝔐.Vgen s := by rw [htop]; trivial
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 he'
    rw [Finsupp.sum_fintype _ _ fun _ => rfl] at he ⊢
    have h1 := mem_of_sum_mem (𝔐.M.lat q) 𝔐.ρ 𝔐.emb
      (fun a e he => lat_stable 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act q a he) (fun s a => hreg s a q) hsep Finset.univ f
      (fun s _ => hf s) he
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.mem_iSup_of_mem s ⟨h1 s (Finset.mem_univ s), hf s⟩
  have hbi : ∀ x, (∀ w ∈ 𝔐.M.omLat q, w x ∈ regAt 𝔐.ξ q) → x ∈ 𝔐.M.lat q := by
    intro x hx
    choose U hU b hb hfr using fun s => 𝔐.vb s q trivial
    rw [hlat]
    refine mem_iSup_of_dual 𝔐.Vgen hind htop (labelRk D) b (fun s => (hfr s q trivial (hU s)).1) hb
      (fun s => 𝔐.dR s q) (fun s => (hV s).symm.trans (hfr s q trivial (hU s)).2) x fun w hw =>
        hx w (show ∀ e ∈ 𝔐.M.lat q, w e ∈ regAt 𝔐.ξ q from fun e he => by
          rw [hlat] at he
          exact Submodule.iSup_induction _ (motive := fun e => w e ∈ regAt 𝔐.ξ q) he hw
            (by simpa using zero_mem _) (fun a b ha hb => by simpa using add_mem ha hb))
  refine ⟨hV, fun p hp s => ?_, hlat⟩
  have hn : unitAt 𝔐.ξ q ((p ^ 𝔐.R p : ℕ) : Ω) := hnat _ (pow_ne_zero _ hp.ne_zero)
  have hd : ∀ s, 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q = 𝔐.dR s q := fun s =>
    htDual_eq_eigLat 𝔐.M 𝔐.ρ _ 𝔐.t.PP.isLB hn hbi
  cases s with
  | inl τ =>
    have hbot : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
    exact htW_eq_eigLat 𝔐.M 𝔐.ρ _ (hd _) (fun d => hreg _ d q) _ (Ideal.absNorm (differentIdeal ℤ (𝓞 E)))
      (Ideal.absNorm_mem _) (hnat _ (by simpa [Ideal.absNorm_eq_zero_iff] using hbot))
  | inr τ => exact hd _

end GlobalTheory.CompanionTheory.Ar.HodgeChar0
