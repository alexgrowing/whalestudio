import Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdLinkOfArchimedean
import Formalism.LocalToGlobal.GlobalTheory.GL4.BcBasisApply
import Mathlib
import Formalism.LocalToGlobal.Columns.FockNormSubstitutionBound
import Formalism.LocalToGlobal.Columns.TwistedLocalisationComparable

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section G

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

def crdQ (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (CV.Q c τ).V ≃ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL) :=
  ((CV.Q c τ).b.reindex (CV.eQ c τ)).equivFun

def MQ (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Submodule (𝓞 D.what₂.LL) (Fin (D.R.N 0) → D.what₂.LL) :=
  (CV.Q c τ).L.map ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL))

def gM (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  Matrix.of fun a i => bcFun CV c τ (y a) ((CV.Q c τ).b ((CV.eQ c τ).symm i))

theorem gM_mulVec (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (z : (CV.Q c τ).V)
    (a : Fin (D.R.N 0)) : (gM CV c y τ *ᵥ crdQ CV c τ z) a = bcFun CV c τ (y a) z := by
  show ∑ i, gM CV c y τ a i * crdQ CV c τ z i = _
  conv_rhs => rw [← ((CV.Q c τ).b.reindex (CV.eQ c τ)).sum_equivFun z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Basis.reindex_apply, mul_comm]
  rfl

theorem gM_int (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (τ : D.what₂.Tau) :
    ∀ x ∈ MQ CV c τ, ∀ a, (gM CV c y τ *ᵥ x) a ∈ (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL) := by
  rintro _ ⟨z, hz, rfl⟩ a
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, gM_mulVec]
  exact Submodule.mem_one.2 ⟨⟨_, bcFun_int CV c τ (hy a) hz⟩, rfl⟩

theorem gM_unit (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (τ : D.what₂.Tau) : IsUnit (gM CV c y τ).det := by
  classical
  have hn : Fintype.card (Fin (D.R.N 0)) = finrank D.host.E (D.sp.X 0).V := by
    rw [Fintype.card_fin, (D.sp.X 0).rank_eq, D.sp.rank0, Ranks.N_zero]
  haveI : Nonempty (Fin (D.R.N 0)) := ⟨⟨0, rank_zero_pos D⟩⟩
  haveI : FiniteDimensional D.host.E (D.sp.X 0).V :=
    Module.finite_of_finrank_pos (by rw [← hn]; exact Fintype.card_pos)
  have hspan := hli.span_eq_top_of_card_eq_finrank hn
  let Φ : (D.sp.X 0).V →ₗ[D.host.E] (Fin (D.R.N 0) → D.host.E) := LinearMap.pi fun a => (D.sp.X 0).hT (y a)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ a, (D.sp.X 0).hT (y a) z = 0 := fun a => congrFun (LinearMap.mem_ker.1 hz) a
    refine (D.sp.X 0).nondeg.2 z fun x => ?_
    have hx : x ∈ Submodule.span D.host.E (Set.range y) := hspan ▸ Submodule.mem_top
    have hx' := (Submodule.span_le (p := LinearMap.ker ((D.sp.X 0).hT.flip z))).2 (by
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.2 (by rw [LinearMap.flip_apply]; exact h0 a)) hx
    have := LinearMap.mem_ker.1 hx'
    rwa [LinearMap.flip_apply] at this
  have hfin : finrank D.host.E (D.sp.X 0).V = finrank D.host.E (Fin (D.R.N 0) → D.host.E) := by
    rw [Module.finrank_fin_fun, ← hn, Fintype.card_fin]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  rw [← Matrix.isUnit_iff_isUnit_det]
  refine Matrix.linearIndependent_rows_iff_isUnit.1 ?_
  rw [Fintype.linearIndependent_iff]
  intro t ht b
  obtain ⟨z, hz⟩ := hsurj (Pi.single b 1)
  have hz' : ∀ a, (D.sp.X 0).hT (y a) z = (Pi.single b (1 : D.host.E) : Fin (D.R.N 0) → D.host.E) a := fun a => congrFun hz a
  have hi : ∀ i, ∑ a, t a * gM CV c y τ a i = 0 := fun i => by
    have := congrFun ht i
    simpa [Finset.sum_apply] using this
  have key : ∑ a, t a * CV.rho τ ((D.sp.X 0).hT (y a) z) = 0 := by
    have e1 : ∀ a, CV.rho τ ((D.sp.X 0).hT (y a) z) = ∑ i, gM CV c y τ a i * crdQ CV c τ (CV.bc c τ z) i := by
      intro a
      rw [← bcFun_bc CV c τ (y a) z, ← gM_mulVec CV c y τ]
      rfl
    simp_rw [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hi i, zero_mul]
  simpa [hz', Pi.single_apply] using key

def gG (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y) :
    D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL :=
  fun τ => Matrix.nonsingInvUnit _ (gM_unit CV c y hli τ)

theorem gG_coe (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (τ : D.what₂.Tau) : ((gG CV c y hli τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) =
      gM CV c y τ := rfl

end G

section Loc

variable {D : D7}

theorem coeff_mem_of_intSpanAt {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n)
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL} (hp : p ∈ IntSpanAt D w lam) (m : (D.what₂.Tau × Fin n × Fin n) →₀ ℕ) :
    coeff m p ∈ intW D.what₂.places w := by
  unfold IntSpanAt at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, -, rfl⟩ := hx
    have hten : Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)) =
        MvPolynomial.map (Int.castRingHom D.what₂.LL) (∏ τ, rename (fun v => (τ, v)) (f τ)) := by
      unfold Formalism.MainNotions.flipTwoThree.ten
      rw [map_prod]
      all_goals exact Finset.prod_congr rfl fun τ _ => by rw [MvPolynomial.map_rename]
    rw [MvPolynomial.coeff_smul, hten, MvPolynomial.coeff_map, smul_eq_mul]
    exact (intW D.what₂.places w).mul_mem hr (intCast_mem _ _)
  | zero =>
    rw [MvPolynomial.coeff_zero]
    exact (intW D.what₂.places w).zero_mem
  | add x y _ _ hx hy =>
    rw [MvPolynomial.coeff_add]
    exact (intW D.what₂.places w).add_mem hx hy
  | neg x _ hx =>
    rw [MvPolynomial.coeff_neg]
    exact (intW D.what₂.places w).neg_mem hx

theorem intW_mem_locRing (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ∈ intW D.what₂.places w) : x ∈ locRing (D.plEq w) := by
  show x ∈ localization₂ (D.plEq w).asIdeal (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL)
  have h1 : (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL) = latOf (K := D.what₂.LL) (fun _ : Unit => (1 : D.what₂.LL)) := by
    rw [Submodule.one_eq_span]
    unfold latOf
    rw [Set.range_const]
  rw [h1, mem_localization_latticeOf_iff, Set.range_const, Submodule.mem_span_singleton]
  exact ⟨⟨x, hx⟩, by rw [Subring.smul_def, smul_eq_mul, mul_one]⟩

theorem mem_localization_map_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (P : Ideal (𝓞 K)) [P.IsPrime] (e : V ≃ₗ[K] W) (A : Submodule (𝓞 K) V) (x : V) :
    e x ∈ localization₂ P (A.map ((e : V →ₗ[K] W).restrictScalars (𝓞 K))) ↔ x ∈ localization₂ P A := by
  show (∃ s ∈ P.primeCompl, s • e x ∈ A.map ((e : V →ₗ[K] W).restrictScalars (𝓞 K))) ↔
    ∃ s ∈ P.primeCompl, s • x ∈ A
  have key : ∀ (s : 𝓞 K) (x : V), e (s • x) = s • e x := fun s x =>
    (e : V →ₗ[K] W).map_smul_of_tower s x
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨z, hz, hze⟩ := Submodule.mem_map.mp hx
    refine ⟨s, hs, ?_⟩
    have hzx : z = s • x := e.injective (by rw [key]; exact hze)
    rwa [← hzx]
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, Submodule.mem_map.mpr ⟨s • x, hx, by
      rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]⟩⟩

end Loc

section Int

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem colLat_eq_map (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : GL (Fin (D.R.N 0)) D.what₂.LL) :
    colLat B = (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) =>
      ∑ i, (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)).map
        ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL)) := by
  have hb : ∀ i, crdQ CV c τ ((CV.Q c τ).b ((CV.eQ c τ).symm i)) = Pi.single i 1 := by
    intro i
    unfold crdQ
    rw [← Basis.reindex_apply]
    ext j
    simp [Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  unfold latOf colLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span _) (congrArg Set.range ?_)
  funext j a
  simp only [Function.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, map_sum, map_smul, hb]
  simp [Pi.single_apply]

theorem locBasis_of_isBasisAt (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (w : D.what₂.places.Pl) (B : GL (Fin (D.R.N 0)) D.what₂.LL)
    (hB : IsBasisAt (D.plEq w) (MQ CV c τ) B) :
    LocBasis D w (CV.Q c τ) (CV.eQ c τ) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mp B.isUnit, ?_⟩
  ext x
  rw [← mem_localization_iff_localizationAtPlace, ← mem_localization_latticeOf_iff D w,
    ← mem_localization_map_equiv (D.plEq w).asIdeal (crdQ CV c τ) (CV.Q c τ).L x,
    ← mem_localization_map_equiv (D.plEq w).asIdeal (crdQ CV c τ)
      (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) =>
        ∑ i, (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) x,
    ← colLat_eq_map CV c τ B]
  change crdQ CV c τ x ∈ localization₂ (D.plEq w).asIdeal (MQ CV c τ) ↔ _
  rw [hB]

end Int

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
