import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantEuclideanComplex
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel

noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneFormTest

section Abstract

variable {K : Type} [Field K] {σ : K →+* ℂ} {E : Type} [AddCommGroup E] [Module ℂ E]
  {V : Type} [AddCommGroup V] [Module K V]

theorem exists_coord {I : Type} (ψ : I → E →ₗ[ℂ] ℂ) (ι : V →ₛₗ[σ] E) (h : ∀ x a, ∃ z : K, σ z = ψ a (ι x)) :
    ∃ f : V →ₗ[K] (I → K), ∀ x a, σ (f x a) = ψ a (ι x) := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => funext fun a => σ.injective ?_⟩, fun c x => funext fun a => σ.injective ?_⟩, hf⟩
  · rw [Pi.add_apply, map_add, hf, hf, hf, map_add, map_add]
  · simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hf, map_smulₛₗ]

theorem semi_apply_pi {n : ℕ} (ι : (Fin n → K) →ₛₗ[σ] E) (u : Fin n → K) :
    ι u = ∑ a, σ (u a) • ι (Pi.single a 1) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (Pi.single a (u a) : Fin n → K) = u a • Pi.single a 1 := by
    funext i; by_cases hi : i = a <;> simp [hi]
  rw [this, map_smulₛₗ]

theorem mem_span_of_ker {H : Type} [AddCommGroup H] [Module ℂ H] {n : ℕ} (ψ : Fin n → E →ₗ[ℂ] ℂ)
    (hψ : ∀ e, (∀ a, ψ a e = 0) → e = 0) (j : V →ₛₗ[σ] H) (hj : Submodule.span ℂ (Set.range j) = ⊤) (Θ : H →ₗ[ℂ] E)
    (h : ∀ x a, ∃ z : K, σ z = ψ a (Θ (j x))) {y : H} (hy : Θ y = 0) :
    y ∈ Submodule.span ℂ (j '' {x | Θ (j x) = 0}) := by
  obtain ⟨f, hf⟩ := exists_coord ψ (Θ.comp j) h
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict f.range_rangeRestrict
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype (Submodule.ker_subtype _)
  have hfg : ∀ x, f (s (p (f x))) = f x := fun x => by
    have h1 : p (f x) = f.rangeRestrict x := congrArg (fun L => L (f.rangeRestrict x)) hp
    have h2 : f.rangeRestrict (s (f.rangeRestrict x)) = f.rangeRestrict x := congrArg (fun L => L (f.rangeRestrict x)) hs
    rw [h1]
    exact congrArg Subtype.val h2
  let L : H →ₗ[ℂ] H := ∑ a, (ψ a ∘ₗ Θ).smulRight (j (s (p (Pi.single a 1))))
  have hL : ∀ y, L y = ∑ a, ψ a (Θ y) • j (s (p (Pi.single a 1))) := fun y => by
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]
  have hLj : ∀ x, L (j x) = j (s (p (f x))) := fun x => by
    rw [hL]
    refine Eq.trans ?_ (semi_apply_pi (j.comp (s ∘ₗ p)) (f x)).symm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hf]
    rfl
  have key : Submodule.span ℂ (Set.range j) ≤
      (Submodule.span ℂ (j '' {x | Θ (j x) = 0})).comap (LinearMap.id - L) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    change j x - L (j x) ∈ Submodule.span ℂ _
    rw [hLj, ← map_sub]
    refine Submodule.subset_span ⟨_, hψ _ fun a => ?_, rfl⟩
    have := hf (x - s (p (f x))) a
    rw [map_sub, hfg, sub_self, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 : y - L y ∈ Submodule.span ℂ (j '' {x | Θ (j x) = 0}) := key (hj ▸ Submodule.mem_top)
  rwa [hL, hy, Finset.sum_eq_zero fun a _ => by rw [map_zero, zero_smul], sub_zero] at h3

theorem exists_orth [FiniteDimensional K V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : V →ₛₗ[σ] H)
    (hj : Function.Injective j) (hr : ∀ x y, ∃ z : K, σ z = ⟪j x, j y⟫_ℂ) (U : Submodule K V) (x : V) :
    ∃ k ∈ U, ∀ k' ∈ U, ⟪j k', j (x - k)⟫_ℂ = 0 := by
  let b := Module.finBasis K U
  obtain ⟨f, hf⟩ := exists_coord (fun i => innerₛₗ ℂ (j (b i : V))) j fun y i => hr _ y
  have horth : ∀ y, f y = 0 → ∀ k' ∈ U, ⟪j k', j y⟫_ℂ = 0 := by
    intro y hy k' hk'
    have e : k' = ∑ i, b.repr ⟨k', hk'⟩ i • (b i : V) := by
      have := congrArg U.subtype (b.sum_repr ⟨k', hk'⟩)
      rw [map_sum] at this
      exact this.symm
    rw [e, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : ⟪j (b i : V), j y⟫_ℂ = 0 := by
      have := hf y i
      rw [hy, Pi.zero_apply, map_zero] at this
      exact this.symm
    rw [map_smulₛₗ, inner_smul_left, h0, mul_zero]
  have hinj : Function.Injective (f ∘ₗ U.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have := horth u hu u u.2
    rw [inner_self_eq_zero, ← map_zero j] at this
    exact Subtype.ext (hj this)
  have hsurj : Function.Surjective (f ∘ₗ U.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨k, hk⟩ := hsurj (f x)
  exact ⟨k, k.2, horth _ (by rw [map_sub, ← hk]; exact sub_self _)⟩

end Abstract

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K) {E : Type} [AddCommGroup E] [Module ℂ E]

theorem injective_and_rat {n d : ℕ} (ψ : Fin n → E →ₗ[ℂ] ℂ) (hψ : ∀ e, (∀ a, ψ a e = 0) → e = 0)
    (ι : (Fin d → ℂ) →ₗ[ℂ] E) (h : ∀ x a, ∃ z : K, v.embedding z = ψ a (ι (cpt v.embedding x)))
    (hι : ∀ x : Fin d → K, ι (cpt v.embedding x) = 0 → x = 0) :
    Function.Injective ι ∧
      ∀ w, (∀ a, ∃ z : K, v.embedding z = ψ a (ι w)) → ∃ y : Fin d → K, cpt v.embedding y = w := by
  obtain ⟨f, hf⟩ := exists_coord ψ (ι.comp (cptL v.embedding d)) h
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine hι x (hψ _ fun a => ?_)
    have := hf x a
    rw [hx, Pi.zero_apply, map_zero] at this
    exact this.symm
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let L : E →ₗ[ℂ] (Fin d → ℂ) := ∑ a, (ψ a).smulRight (cpt v.embedding (g (Pi.single a 1)))
  have hL : ∀ (e : E) (u : Fin n → K), (∀ a, v.embedding (u a) = ψ a e) → L e = cpt v.embedding (g u) := fun e u hu => by
    refine Eq.trans ?_ (semi_apply_pi ((cptL v.embedding d).comp g) u).symm
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply, hu]
    rfl
  have hid : L ∘ₗ ι = LinearMap.id := by
    refine GlobalTheory.EquivariantEuclideanComplex.ext_cpt v fun x => ?_
    rw [LinearMap.comp_apply, hL (ι (cpt v.embedding x)) (f x) (hf x), LinearMap.id_apply]
    exact congrArg _ (congrArg (fun M => M x) hg)
  have hid' : ∀ w, L (ι w) = w := fun w => congrArg (fun M => M w) hid
  refine ⟨Function.LeftInverse.injective hid', fun w hw => ?_⟩
  choose u hu using hw
  exact ⟨g u, (hL _ u hu).symm.trans (hid' w)⟩

end Coord

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J} (X : CxData F.amb)

structure FormsTie : Prop where

  inner_eq : ∀ t (x y : (F.R t).S.Forms),
    ⟪X.jR t x, X.jR t y⟫_ℂ = F.v0.embedding ((F.R t).S.csum (x : (F.R t).S.Cl → (F.R t).S.V) (y : (F.R t).S.Cl → (F.R t).S.V))

  inj : ∀ t, Function.Injective (X.jR t)

  span : ∀ t, Submodule.span ℂ (Set.range (X.jR t)) = ⊤

def ThroughGood : Prop :=
  ∀ t (x : (F.R t).S.Forms), X.Θ t (X.jR t ((F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) x)) = X.Θ t (X.jR t x)

omit X in
theorem csum_gaOp_good (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (hB : B.Ok s)
    {Y : Finset (G → K)} (hY : ∀ χ ∈ Y, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (x y : B.S.Forms) :
    B.S.csum (B.S.gaOp B.r (goodAt Y P ψ) x : B.S.Cl → B.S.V) (y : B.S.Cl → B.S.V) =
      B.S.csum (x : B.S.Cl → B.S.V) (B.S.gaOp B.r (goodAt Y P ψ) y : B.S.Cl → B.S.V) := by
  have hp := good_at_spec K v0 hv0 G Y hY P ψ
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt Y P ψ)
  rw [hp.selfAdj] at hadj
  have e : ∀ a b : B.S.Forms, B.S.csum (a : B.S.Cl → B.S.V) (b : B.S.Cl → B.S.V) =
      hform B.S.H (B.S.basis.equivFun a) (B.S.basis.equivFun b) := fun a b => by
    have := B.S.isClassSum (B.S.basis.equivFun a) (B.S.basis.equivFun b)
    rw [CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  rw [e, e, ← CSD.gaMat_mulVec_equivFun, ← CSD.gaMat_mulVec_equivFun, RationalHermitianForm.hform_eq_dot, RationalHermitianForm.hform_eq_dot,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hadj]

variable {X}

theorem exists_mem_range_toF {s : ℕ} (hF : F.Ok s) (hT : FormsTie X) (hg : ThroughGood X)
    (hr : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTest X) (t : T) (x : (F.R t).S.Forms) :
    ∃ z ∈ LinearMap.range ((F.R t).toF (F.lvl ⊥ 1) (X.Z t)), X.Θ t (X.jR t z) = X.Θ t (X.jR t x) := by
  obtain ⟨n, ψ, hψ, hrat⟩ := hr
  haveI : FiniteDimensional K (F.amb.FR t) := Module.Finite.of_basis (F.R t).S.basis
  obtain ⟨k, hk, horth⟩ := exists_orth (X.jR t) (hT.inj t) (fun a b => ⟨_, (hT.inner_eq t a b).symm⟩)
    (LinearMap.ker ((X.Θ t).comp (X.jR t))) x
  have hk' : X.Θ t (X.jR t k) = 0 := hk
  refine ⟨(F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) (x - k), ?_, ?_⟩
  · rw [GlobalTheory.OneForm.range_toF]
    refine ⟨?_, x - k, ?_⟩
    · change X.jR t _ ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))
      rw [← LinearMap.orthogonal_ker, Submodule.mem_orthogonal]
      intro u hu
      refine GlobalTheory.EquivariantEuclideanComplex.orth_span ?_ u (mem_span_of_ker ψ hψ (X.jR t) (hT.span t) (X.Θ t) (hrat t) hu)
      rintro _ ⟨a, ha, rfl⟩
      have h1 := horth ((F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) a) ((hg t a).trans ha)
      refine ((hT.inner_eq t _ _).trans ?_).trans (((hT.inner_eq t _ _).symm).trans h1)
      rw [csum_gaOp_good (F.R t) hF.conj (hF.what₂ t) hF.irr]
    · rw [GlobalTheory.OneForm.asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]
      rfl
  · refine (hg t _).trans ?_
    have e : X.jR t (x - k) = X.jR t x - X.jR t k := map_sub (X.jR t) x k
    exact (congrArg (X.Θ t) e).trans (by rw [map_sub, hk', sub_zero])

theorem bijective_and_ratMu {s : ℕ} (hF : F.Ok s) (hT : FormsTie X) (hg : ThroughGood X)
    (hr : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTest X) (hon : ∀ t, Function.Surjective (X.Θ t))
    {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool) (hc : GlobalTheory.EquivariantEuclideanComplex.IsCoord cr b X.zs ⊥ 1) :
    (∀ t, Function.Bijective (X.iC cr b t)) ∧ X.RATmu cr b := by
  have hex := exists_mem_range_toF hF hT hg hr
  obtain ⟨n, ψ, hψ, hrat⟩ := hr
  have key := fun t => injective_and_rat F.v0 ψ hψ (X.iC cr b t)
    (fun x a => by
      obtain ⟨z, hz⟩ := hrat t (cr.toR X.zs b t x) a
      exact ⟨z, hz.trans (congrArg (ψ a) (GlobalTheory.OneForm.iC_cpt X cr b t x).symm)⟩)
    (fun x hx => by
      have h0 : X.Θ t (X.jR t (cr.toR X.zs b t x)) = 0 := (GlobalTheory.OneForm.iC_cpt X cr b t x).symm.trans hx
      have h1 : cr.toR X.zs b t x ∈ LinearMap.range ((F.R t).toF (F.lvl ⊥ 1) (X.zs.Z t)) := (hc t).2 ▸ ⟨x, rfl⟩
      rw [GlobalTheory.OneForm.range_toF] at h1
      obtain ⟨y, hy⟩ : X.jR t (cr.toR X.zs b t x) ∈ LinearMap.range (LinearMap.adjoint (X.Θ t)) := h1.1
      have h2 : ⟪X.jR t (cr.toR X.zs b t x), X.jR t (cr.toR X.zs b t x)⟫_ℂ = 0 := by
        conv_lhs => enter [2]; rw [← hy]
        rw [LinearMap.adjoint_inner_left, h0, inner_zero_right]
      rw [inner_self_eq_zero, ← map_zero (X.jR t)] at h2
      exact (hc t).1 ((hT.inj t h2).trans (map_zero _).symm))
  have hsur : ∀ t, Function.Surjective (X.iC cr b t) := fun t => by
    have h1 : Submodule.span ℂ (Set.range (X.jR t)) ≤ (LinearMap.range (X.iC cr b t)).comap (X.Θ t) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      obtain ⟨z, hz, e⟩ := hex t x
      obtain ⟨y, rfl⟩ : z ∈ LinearMap.range (cr.toR X.zs b t) := (hc t).2.symm ▸ hz
      exact ⟨_, (GlobalTheory.OneForm.iC_cpt X cr b t y).trans e⟩
    intro e
    obtain ⟨u, rfl⟩ := hon t e
    exact h1 (hT.span t ▸ Submodule.mem_top)
  refine ⟨fun t => ⟨(key t).1, hsur t⟩, GlobalTheory.OneForm.rat_of_image_le X cr b (key F.μ0).1 fun t y _ => ?_⟩
  obtain ⟨w, hw⟩ := hsur F.μ0 (X.Θ t (X.jR t y))
  obtain ⟨y₀, rfl⟩ := (key F.μ0).2 w fun a => by
    obtain ⟨z, hz⟩ := hrat t y a
    exact ⟨z, hz.trans (congrArg (ψ a) hw.symm)⟩
  exact ⟨_, ⟨y₀, rfl⟩, (GlobalTheory.OneForm.iC_cpt X cr b F.μ0 y₀).symm.trans hw⟩

end Family

end GlobalTheory.OneFormTest
