import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupported
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.LabelTransport

open Classical in

theorem coset_transport {G H : Type} [Group G] [Group H] (ψ : G →* H) (T U J : Subgroup G) (K : Set H) (α : H)
    (R : Finset H) (hK : ∀ x, ψ x ∈ K ↔ x ∈ U ∧ x ∈ T) (hKr : ∀ k ∈ K, ∃ x, ψ x = k)
    (hJ : ∀ x ∈ T, x ∈ J ↔ x ∈ U) (pre : H → G) (hpre : ∀ γ ∈ R, ψ (pre γ) = γ ∧ pre γ ∈ T)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : H, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    ∃ Ds : Set G, (∀ x ∈ Ds, x ∈ T) ∧ (∀ x ∈ Ds, ∀ κ ∈ U, κ ∈ T → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧
      {c : G ⧸ J | ∃ x ∈ Ds, (x : G ⧸ J) = c}.Finite ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), (∀ x, ∀ κ ∈ J, κ ∈ T → F (x * κ) = F x) → ∀ g,
        (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ Ds, (x : G ⧸ J) = c then F (g * hc.choose) else 0) = ∑ γ ∈ R, F (g * pre γ) := by
  have hmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := hKr a ha
    obtain ⟨y, rfl⟩ := hKr b hb
    rw [← map_mul, hK]
    exact ⟨mul_mem ((hK x).1 ha).1 ((hK y).1 hb).1, mul_mem ((hK x).1 ha).2 ((hK y).1 hb).2⟩
  let Ds : Set G := {x | x ∈ T ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ψ x = k₁ * α * k₂}
  have hpD : ∀ γ ∈ R, pre γ ∈ Ds := fun γ hγ => ⟨(hpre γ hγ).2, by rw [(hpre γ hγ).1]; exact h1 γ hγ⟩
  have hrel : ∀ γ ∈ R, ∀ x ∈ T, ((pre γ : G ⧸ J) = (x : G ⧸ J) ↔ γ⁻¹ * ψ x ∈ K) := by
    intro γ hγ x hx
    have ht : (pre γ)⁻¹ * x ∈ T := mul_mem (inv_mem (hpre γ hγ).2) hx
    have e : ψ ((pre γ)⁻¹ * x) = γ⁻¹ * ψ x := by rw [map_mul, map_inv, (hpre γ hγ).1]
    rw [QuotientGroup.eq, hJ _ ht, ← e, hK]
    exact (and_iff_left ht).symm
  have hset : ∀ c : G ⧸ J, (∃ x ∈ Ds, (x : G ⧸ J) = c) ↔ c ∈ R.image fun γ => (pre γ : G ⧸ J) := by
    intro c
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 _ hx.2
      exact ⟨γ, hγ, (hrel γ hγ x hx.1).2 e⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨_, hpD γ hγ, rfl⟩
  refine ⟨Ds, fun x hx => hx.1, ?_, ?_, ?_⟩
  · rintro x ⟨hx, a, ha, b, hb, e⟩ κ hκ hκ'
    have hk : ψ κ ∈ K := (hK κ).2 ⟨hκ, hκ'⟩
    refine ⟨⟨mul_mem hx hκ', a, ha, _, hmul b hb _ hk, ?_⟩, ⟨mul_mem hκ' hx, _, hmul _ hk a ha, b, hb, ?_⟩⟩
    · rw [map_mul, e, mul_assoc]
    · rw [map_mul, e]; simp only [mul_assoc]
  · exact (R.image fun γ => (pre γ : G ⧸ J)).finite_toSet.subset fun c hc => (hset c).1 hc
  · intro W _ F hF g
    rw [finsum_eq_sum_of_support_subset (s := R.image fun γ => (pre γ : G ⧸ J))]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun γ hγ => ?_
        have hc : ∃ x ∈ Ds, (x : G ⧸ J) = (pre γ : G ⧸ J) := ⟨_, hpD γ hγ, rfl⟩
        rw [dif_pos hc]
        have hj : hc.choose⁻¹ * pre γ ∈ J := QuotientGroup.eq.1 hc.choose_spec.2
        have ht : hc.choose⁻¹ * pre γ ∈ T := mul_mem (inv_mem hc.choose_spec.1.1) (hpre γ hγ).2
        rw [← hF (g * hc.choose) _ hj ht, mul_assoc, mul_inv_cancel_left]
      · intro a ha b hb e
        have ha' : a ∈ R := ha
        have hb' : b ∈ R := hb
        have e1 := (hrel a ha' _ (hpre b hb').2).1 e
        have e2 := (hrel b hb' _ (hpre b hb').2).1 rfl
        rw [(hpre b hb').1] at e1 e2
        exact (h2 b (h1 b hb')).unique ⟨ha', e1⟩ ⟨hb', e2⟩
    · intro c hc
      by_contra hn
      exact hc (dif_neg fun h => hn ((hset c).1 h))

theorem tensCast_under {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (P : HeightOneSpectrum (𝓞 E)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α (P.under (𝓞 F1)) = 1)
    (h0 : ∀ v', v' ≠ P.under (𝓞 F1) → α v' = 0) :
    ∃ α' : FiniteAdeleRing (𝓞 F2) F2,
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' (P.under (𝓞 F2)) = 1 ∧
        ∀ v', v' ≠ P.under (𝓞 F2) → α' v' = 0 := by
  subst h
  exact ⟨α, rfl, h1, h0⟩

theorem idem_mul_iff {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (α : AFplus L) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0)
    (z : AL L) : ((1 : L) ⊗ₜ[maximalRealSubfield L] α) * z = z ↔ ∀ v', v' ≠ v → compAt L v' z = 0 := by
  have hc : ∀ u, compAt L u ((1 : L) ⊗ₜ[maximalRealSubfield L] α) = (1 : L) ⊗ₜ[maximalRealSubfield L] (α u) := by
    intro u
    rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  constructor
  · intro h u hu
    rw [← h, map_mul, hc, h0 u hu, TensorProduct.tmul_zero, zero_mul]
  · intro h
    rw [← sub_eq_zero]
    apply GlobalTheory.AL_eq_zero_of_compAt
    intro u
    rw [map_sub, map_mul, hc]
    by_cases hu : u = v
    · subst hu
      rw [h1, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [h u hu, mul_zero, sub_zero]

theorem conj_supp {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (M : Matrix (Fin m) (Fin m) B)
    (hM : M = β * K * β') (h : ∀ i j, φ * (K - 1) i j = (K - 1) i j) : ∀ i j, φ * (M - 1) i j = (M - 1) i j := by
  have e : M - 1 = β * (K - 1) * β' := by
    rw [hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have e1 : φ • (K - 1) = K - 1 := Matrix.ext h
  have e2 : φ • (β * (K - 1) * β') = β * (K - 1) * β' := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  rw [e]
  exact fun i j => congrFun (congrFun e2 i) j

theorem conj_supp_iff {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (h2 : β' * β = 1)
    (M : Matrix (Fin m) (Fin m) B) (hM : M = β * K * β') :
    (∀ i j, φ * (M - 1) i j = (M - 1) i j) ↔ ∀ i j, φ * (K - 1) i j = (K - 1) i j := by
  refine ⟨conj_supp φ β' M β h2 K ?_, conj_supp φ β K β' h1 M hM⟩
  rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 2000000 in

theorem suppF_iff_trivOutside (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV)
    (e f : Formalism.L2.Theta.AE D) (hef : Formalism.IndefR.Mult.IsPrimeIdem s.w e f) (κ : GAf D.host.E n) :
    Formalism.IndefR.Mult.SuppF V f (PV.ψ κ) ↔ TrivOutside {s.v} κ := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, hα1, hα0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hef
  obtain ⟨α', hT, hw1, hw0⟩ := tensCast_under hF s.w α hα1 hα0
  have hv : s.w.under (𝓞 (maximalRealSubfield D.host.E)) = s.v := HeightOneSpectrum.ext s.w_under
  rw [hv] at hw1 hw0
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  have hfin : Formalism.L2.Theta.finPart D x = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  set K := (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm with hKdef
  set M := (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.finPart D) with hMdef
  have e6 : (Formalism.L2.Theta.mt V (PV.ψ κ) - 1).map (Formalism.L2.Theta.finPart D) = M - 1 := by
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.finPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.finPart D)) (map_one (Formalism.L2.Theta.finPart D))]
  have e2 : ((Formalism.L2.Theta.mt V (PV.ψ κ)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
    have hk := MonoidHom.mem_ker.1 (PV.into κ)
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
    have e3 : (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ κ)).val := rfl
    rw [e3, hk, Units.val_one, sub_self]
  have s1 : Formalism.IndefR.Mult.SuppF V x (PV.ψ κ) ↔ ∀ i j, Formalism.L2.Theta.finPart D x * (M - 1) i j = (M - 1) i j := by
    rw [← e6]
    refine forall_congr' fun i => forall_congr' fun j => ⟨fun h => ?_, fun h => ?_⟩
    · exact ((Formalism.L2.Theta.finPart D).map_mul _ _).symm.trans (congrArg (Formalism.L2.Theta.finPart D) h)
    · rw [← sub_eq_zero]
      apply GlobalTheory.PlaceSupp.AE_eq_zero D
      · have h0 : Formalism.L2.Theta.infPart D ((Formalism.L2.Theta.mt V (PV.ψ κ) - 1) i j) = 0 := congrFun (congrFun e2 i) j
        rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_mul, sub_eq_zero]
        exact h
  have s2 := conj_supp_iff (Formalism.L2.Theta.finPart D x) β K β' h1 h2 M (hm κ)
  have e7 : (K - 1).map (GlobalTheory.NJoin.tensCast hF) = (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1 := by
    rw [Matrix.map_sub _ (map_sub (GlobalTheory.NJoin.tensCast hF)),
      Matrix.map_one _ (map_zero (GlobalTheory.NJoin.tensCast hF)) (map_one (GlobalTheory.NJoin.tensCast hF))]
    congr 1
    exact Matrix.ext fun a b => (GlobalTheory.NJoin.tensCast hF).apply_symm_apply ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b)
  have s3 : ∀ i j, Formalism.L2.Theta.finPart D x * (K - 1) i j = (K - 1) i j ↔
      ∀ v', v' ≠ s.v → compAt D.host.E v' (((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j) = 0 := by
    intro i j
    have e8 : GlobalTheory.NJoin.tensCast hF ((K - 1) i j) = ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j :=
      congrFun (congrFun e7 i) j
    rw [← idem_mul_iff s.v α' hw1 hw0, ← (GlobalTheory.NJoin.tensCast hF).injective.eq_iff, (GlobalTheory.NJoin.tensCast hF).map_mul,
      hfin, hT, e8]
  have e9 : ∀ v', ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1).map (compAt D.host.E v') =
      (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E v') - 1 := fun v' => by
    rw [Matrix.map_sub _ (map_sub (compAt D.host.E v')),
      Matrix.map_one _ (map_zero (compAt D.host.E v')) (map_one (compAt D.host.E v'))]
  rw [s1, s2]
  constructor
  · intro h v' hv'
    rw [← sub_eq_zero, ← e9]
    exact Matrix.ext fun i j => (s3 i j).1 (h i j) v' hv'
  · intro h i j
    refine (s3 i j).2 fun v' hv' => ?_
    have := e9 v'
    rw [h v' hv', sub_self] at this
    exact congrFun (congrFun this i) j

set_option maxHeartbeats 2000000 in

theorem transport_label : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (sp : SplitPlace D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (sp.w.under (𝓞 D.host.F)) → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) sp.w d → ∃ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) ∧ (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧ {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite ∧ ∀ (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (c : ℂ), (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d, X.fn hμ j f (g * γ) = c • X.fn hμ j f g) → NG.heckeD (P.M.loc i).J Ds ((P.M.loc i).real (hj ▸ f)) = c • (P.M.loc i).real (hj ▸ f) := by
  intro _ hL D P X hA _ _ _ i hμ j hj sp _ _ hJ d hd
  classical
  obtain ⟨e, f, ϖ, α, -, hef, -, -, -, -, -, -, -, hRs, hR1, hR2⟩ := GlobalTheory.SphLabelOps.sphOp_rep hd
  have hsupp := suppF_iff_trivOutside D sp hA.hF _ _ (hA.PV j) (hA.stdV j) e f hef
  have hpre : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
      (hA.PV j).ψ (Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) = γ := by
    intro γ hγ
    have h := (hA.PV j).onto γ (hR1 γ hγ).1
    rw [Formalism.IndefR.principalLevelFrame.pre, dif_pos h]
    exact h.choose_spec
  obtain ⟨Ds, d1, d2, d3, d4⟩ := coset_transport (hA.PV j).ψ (GlobalTheory.InertSph.Gv D.host.E D.R.nV sp.v)
    (Umax D.host.E D.R.nV) (P.M.loc i).J _ α (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d)
    (fun x => and_congr ((hA.stdV j).2 x).symm (hsupp x)) (fun k hk => (hA.PV j).onto k hk.1.1)
    (fun x hx => (hJ x hx).1) (Formalism.IndefR.principalLevelFrame.pre (hA.PV j))
    (fun γ hγ => ⟨hpre γ hγ, (hsupp _).1 (by rw [hpre γ hγ]; exact hRs γ hγ)⟩) (fun γ hγ => (hR1 γ hγ).2) hR2
  refine ⟨Ds, d1, d2, d3, fun φ c hc => ?_⟩
  have key : ∀ (k : ℕ) (ek : j.1 + 1 = k) (k1 : 1 ≤ k) (k2 : k ≤ D.R.m) (g : GAf D.host.E D.R.nV),
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
        (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) (g * Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) =
        c • (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) g := by
    intro k ek k1 k2 g
    subst ek
    have hr := hA.real (D.nd.mu i) hμ j φ
    rw [hr g, ← map_smul, ← hc, map_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hr, ← mul_assoc, map_mul, hpre γ hγ]
  have hty : (P.M.loc i).real (hj ▸ φ) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  funext g
  refine (d4 _ ((P.M.loc i).real (hj ▸ φ)) (fun x κ hκ hκ' => ?_) g).trans (key _ hj _ _ g)
  have h := congrFun (hty.2 ⟨κ, hκ⟩) x
  rw [(hJ κ hκ').2 hκ, Units.val_one, one_smul] at h
  exact h

end GlobalTheory.LabelTransport
