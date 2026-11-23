import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND

section Transport

variable {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V']

theorem integral_map_addEquiv (e : V ≃+ V') (hc : Continuous e) (hc' : Continuous e.symm) (μ : Measure V)
    (f : V' → ℂ) : ∫ y, f y ∂(μ.map e) = ∫ x, f (e x) ∂μ :=
  integral_map_equiv ({ toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' } : V ≃ₜ V').toMeasurableEquiv f

theorem selfDual_map_addEquiv (e : V ≃+ V') (hc : Continuous e) (hc' : Continuous e.symm)
    {μ : Measure V} {χ : V → V → ℂ} {χ' : V' → V' → ℂ} (h : SelfDual μ χ)
    (hχ : ∀ x y, χ' (e x) (e y) = χ x y) : SelfDual (μ.map e) χ' := by
  haveI := h.1
  let H : V ≃ₜ V' := { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  let M : V ≃ᵐ V' := H.toMeasurableEquiv
  have hM : (μ.map e) = μ.map M := rfl
  refine ⟨e.isAddHaarMeasure_map μ hc hc', fun Φ hΦ hs hI z => ?_⟩
  have inner : ∀ y, ∫ x, Φ x * χ' x (e y) ∂(μ.map e) = ∫ x, (Φ ∘ H) x * χ x y ∂μ := by
    intro y
    rw [integral_map_addEquiv e hc hc']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change Φ (e x) * χ' (e x) (e y) = Φ (e x) * χ x y
    rw [hχ]
  have hI0 : Integrable (fun y => ∫ x, (Φ ∘ H) x * χ x y ∂μ) μ := by
    rw [hM] at hI
    have := (M.measurableEmbedding.integrable_map_iff).1 hI
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    change ∫ x, Φ x * χ' x (e y) ∂(μ.map M) = _
    rw [← hM]
    exact inner y
  have key := h.2 (Φ ∘ H) (hΦ.comp H.continuous) (hs.comp_homeomorph H) hI0 (e.symm z)
  have hz : e (e.symm z) = z := e.apply_symm_apply z
  calc ∫ y, (∫ x, Φ x * χ' x y ∂(μ.map e)) * χ' y z ∂(μ.map e)
      = ∫ y, (∫ x, (Φ ∘ H) x * χ x y ∂μ) * χ y (e.symm z) ∂μ := by
        rw [integral_map_addEquiv e hc hc']
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        change (∫ x, Φ x * χ' x (e y) ∂(μ.map e)) * χ' (e y) z = (∫ x, (Φ ∘ H) x * χ x y ∂μ) * χ y (e.symm z)
        rw [inner y, ← hχ y (e.symm z), hz]
    _ = (Φ ∘ H) (-(e.symm z)) := key
    _ = Φ (-z) := by
        change Φ (e (-(e.symm z))) = _
        rw [map_neg, hz]

theorem integral_map_of (f : V → V') (g : V' → V) (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hc : Continuous f) (hc' : Continuous g) (μ : Measure V) (u : V' → ℂ) :
    ∫ y, u y ∂(μ.map f) = ∫ x, u (f x) ∂μ :=
  integral_map_addEquiv ({ toFun := f, invFun := g, left_inv := h1, right_inv := h2, map_add' := hadd } : V ≃+ V') hc hc' μ u

theorem selfDual_map_of (f : V → V') (g : V' → V) (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hc : Continuous f) (hc' : Continuous g)
    {μ : Measure V} {χ : V → V → ℂ} {χ' : V' → V' → ℂ} (h : SelfDual μ χ)
    (hχ : ∀ x y, χ' (f x) (f y) = χ x y) : SelfDual (μ.map f) χ' :=
  selfDual_map_addEquiv ({ toFun := f, invFun := g, left_inv := h1, right_inv := h2, map_add' := hadd } : V ≃+ V') hc hc' h hχ

end Transport

section Tuples

variable {D : D7} {m r : ℕ}

def tupInv (y : Mx D m r) : Fin r → Fin m → AE D := fun a i => y i a

theorem tupOf_tupInv (y : Mx D m r) : tupOf (tupInv y) = y := rfl

theorem tupInv_tupOf (X : Fin r → Fin m → AE D) : tupInv (tupOf X) = X := rfl

theorem tupInv_add (x y : Mx D m r) : tupInv (x + y) = tupInv x + tupInv y := rfl

theorem continuous_tupInv : Continuous (tupInv (D := D) (m := m) (r := r)) :=
  continuous_pi fun a => continuous_pi fun i => continuous_id.matrix_elem i a

theorem continuous_tupOf : Continuous (tupOf (D := D) (m := m) (r := r)) :=
  continuous_matrix fun i a => (continuous_apply i).comp (continuous_apply a)

theorem borel_tup : BorelSpace (Fin r → Fin m → AE D) := by
  obtain ⟨-, -, -, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI : BorelSpace (Fin m → AE D) := Pi.borelSpace
  exact Pi.borelSpace

theorem hR_tup (V : HSp D) (x y : Mx D V.rank r) (a b : Fin r) :
    hR (AF D.host.F) D.sp.cm.sig V.gram (fun i => x i a) (fun i => y i b) = GlobalTheory.StdUnn.inner V x y a b := by
  simp only [hR, Formalism.UG.hform, JR, GlobalTheory.StdUnn.inner, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = (cA D (x i a)) * (incA D (V.gram i j) * y j b)
  rw [mul_assoc]
  rfl

theorem pairing_tup (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D V.rank r) :
    ψ (BR (AF D.host.F) D.sp.cm.sig V.gram (tupInv x) (tupInv y)) = GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ x y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA
  rw [GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
  congr 1
  simp only [BR, Matrix.trace, Matrix.diag, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hR_tup]
  rfl

theorem sdW_map (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {μ : Measure (Mx D V.rank r)}
    {𝓕 : Set (Mx D V.rank r)} (hμ : IsCovolOne (ratMx D V.rank r) μ 𝓕) :
    SdW D.host.F D.host.E D.sp.cm.sig V.rank V.gram (AF D.host.F) ψ r (μ.map tupInv) := by
  obtain ⟨i1, -, -, -, -, -⟩ := lattice_Mx D V.rank r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Fin r → Fin V.rank → AE D) := borel_tup
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  exact selfDual_map_of (χ' := fun X Y => ψ (BR (AF D.host.F) D.sp.cm.sig V.gram X Y)) tupInv tupOf tupOf_tupInv
    tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf
    (GlobalTheory.SiegelWeilLitCompare.selfDual_of_covolOne (isHermND_gram V) hψ hμ) (fun x y => pairing_tup V ψ x y)

end Tuples

section Herm

variable {D : D7} {r : ℕ}

def hermTo (b : hermA D r) : HermR (AF D.host.F) D.sp.cm.sig r := ⟨b.1, fun a c => congrFun (congrFun b.2 a) c⟩

def hermFrom (S : HermR (AF D.host.F) D.sp.cm.sig r) : hermA D r := ⟨S.1, Matrix.ext fun a c => S.2 a c⟩

theorem hermFrom_hermTo (b : hermA D r) : hermFrom (hermTo b) = b := rfl

theorem hermTo_hermFrom (S : HermR (AF D.host.F) D.sp.cm.sig r) : hermTo (hermFrom S) = S := rfl

theorem hermTo_add (x y : hermA D r) : hermTo (x + y) = hermTo x + hermTo y := rfl

theorem continuous_hermTo : Continuous (hermTo (D := D) (r := r)) :=
  continuous_subtype_val.subtype_mk _

theorem continuous_hermFrom : Continuous (hermFrom (D := D) (r := r)) :=
  continuous_subtype_val.subtype_mk _

def trF (a b : Mx D r r) : AF D.host.F := Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (a * b))

theorem trF_comm (a b : Mx D r r) : trF a b = trF b a := by
  unfold trF
  rw [Matrix.trace_mul_comm]

theorem trF_add_left (a a' b : Mx D r r) : trF (a + a') b = trF a b + trF a' b := by
  unfold trF
  rw [Matrix.add_mul, Matrix.trace_add, map_add]

theorem trF_add_right (a b b' : Mx D r r) : trF a (b + b') = trF a b + trF a b' := by
  unfold trF
  rw [Matrix.mul_add, Matrix.trace_add, map_add]

theorem trF_adj (a b : Mx D r r) : trF (adj a) (adj b) = trF a b := by
  have h : Matrix.trace (adj a * adj b) = cA D (Matrix.trace (b * a)) := by
    have e : adj a * adj b = adj (b * a) := (adj_mul b a).symm
    rw [e]
    simp only [Matrix.trace, map_sum]
    rfl
  unfold trF
  rw [h, GlobalTheory.DualPairCheck.trace_cA, Matrix.trace_mul_comm]

theorem half_add_self (p : AF D.host.F) : algebraMap D.host.F (AF D.host.F) (1 / 2) * (p + p) = p := by
  rw [← two_mul, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

def pairH (ψ : AddChar (AF D.host.F) ℂ) (S T : hermA D r) : ℂ :=
  ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * trF S.1 T.1)

theorem pairing_one (ψ : AddChar (AF D.host.F) ℂ) (γ x : Mx D r r) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (1 : Matrix (Fin r) (Fin r) D.host.E) ψ γ x = ψ (trF (adj γ) x) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA trF
  congr 3
  change (adj γ * (1 : Matrix (Fin r) (Fin r) D.host.E).map (incA D)) * x = _
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

theorem isHermND_one : IsHermND D.sp.cm.sig (1 : Matrix (Fin r) (Fin r) D.host.E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]

theorem adj_mem_rat {γ : Mx D r r} (h : γ ∈ ratMx D r r) : adj γ ∈ ratMx D r r := by
  obtain ⟨η, rfl⟩ := mem_ratMx.1 h
  exact mem_ratMx.2 ⟨ηᴴ, rat_conjTranspose η⟩

theorem pairH_annih {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    (∀ x : hermA D r, (∀ γ ∈ ratHerm D r, pairH ψ γ x = 1) ↔ x ∈ ratHerm D r) ∧
      ∀ γ ∈ ratHerm D r, (∀ x, pairH ψ γ x = 1) → γ = 0 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨h1, h2⟩ := GlobalTheory.GramAnnih.ratMx_annihilator D r r 1 isHermND_one ψ hψ
  refine ⟨fun x => ⟨fun h => ?_, fun hx γ hγ => ?_⟩, fun γ hγ h => ?_⟩
  · refine AddSubgroup.mem_comap.2 ((h1 x.1).1 fun γ hγ => ?_)
    have hg : γ + adj γ ∈ hermA D r := by
      change adj (γ + adj γ) = γ + adj γ
      rw [adj_add, adj_adj, add_comm]
    have := h ⟨γ + adj γ, hg⟩ (AddSubgroup.mem_comap.2 (add_mem hγ (adj_mem_rat hγ)))
    rw [pairing_one, ← this]
    unfold pairH
    have hx : adj x.1 = x.1 := x.2
    congr 1
    change _ = _ * trF (γ + adj γ) x.1
    rw [trF_add_left, ← trF_adj γ x.1, hx, half_add_self]
  · obtain ⟨a, ha⟩ := mem_ratMx.1 (AddSubgroup.mem_comap.1 hγ)
    obtain ⟨b, hb⟩ := mem_ratMx.1 (AddSubgroup.mem_comap.1 hx)
    have e : Matrix.trace (γ.1 * x.1) = (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (a * b) := by
      have ha' : rat a = γ.1 := ha
      have hb' : rat b = x.1 := hb
      rw [← ha', ← hb', ← rat_mul]
      exact (AddMonoidHom.map_trace (incA D) _).symm
    unfold pairH trF
    rw [e, GlobalTheory.LatVac.trace_tmul, one_mul, ← map_mul]
    exact hψ.2.2.1 _
  · refine Subtype.ext (h2 γ.1 (AddSubgroup.mem_comap.1 hγ) fun y => ?_)
    have hy : y + adj y ∈ hermA D r := by
      change adj (y + adj y) = y + adj y
      rw [adj_add, adj_adj, add_comm]
    have hγ' : adj γ.1 = γ.1 := γ.2
    have := h ⟨y + adj y, hy⟩
    rw [pairing_one, hγ', ← this]
    unfold pairH
    congr 1
    change _ = _ * trF γ.1 (y + adj y)
    rw [trF_add_right]
    have e : trF γ.1 (adj y) = trF γ.1 y := by
      conv_lhs => rw [← hγ']
      exact trF_adj _ _
    rw [e, half_add_self]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem sdHerm_map {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {lam : Measure (hermA D r)}
    {𝓖 : Set (hermA D r)} (hl : IsCovolOneH lam 𝓖) :
    SdHerm D.host.F D.host.E D.sp.cm.sig (AF D.host.F) ψ r (lam.map hermTo) := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D r) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  haveI : IsTopologicalAddGroup (Matrix (Fin r) (Fin r) (AE D)) := i1
  haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig r) := ⟨rfl⟩
  obtain ⟨hd, K, hK, hKc⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  obtain ⟨h1, h2⟩ := pairH_annih (r := r) hψ
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hsd : SelfDual lam (pairH ψ) := by
    refine GlobalTheory.T.selfDual_of_fundamentalDomain_volume_eq_one _ (ratHerm D r) K hK hKc _ (fun y => ?_) (fun x y => ?_) (fun x x' y => ?_) (fun x y => hψ.2.1 _)
      h1 h2 lam 𝓖 hl.1 hl.2.1 hl.2.2
    · unfold trF
      exact hψ.1.comp (continuous_const.mul (ht.comp
        ((continuous_subtype_val.matrix_mul continuous_const).matrix_trace)))
    · rw [trF_comm]
    · change ψ (_ * trF (x.1 + x'.1) y.1) = _
      rw [trF_add_left, mul_add, AddChar.map_add_eq_mul]
  refine selfDual_map_of (hermTo (D := D) (r := r)) hermFrom hermFrom_hermTo hermTo_hermFrom hermTo_add continuous_hermTo
    continuous_hermFrom hsd fun S T => ?_
  unfold pairH trF pairHerm
  congr 3

end Herm

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem whit_eq_coefN : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ μ : Measure (Mx D V.rank r), (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) →
  ∀ lam : Measure (hermA D r), (∃ 𝓖, IsCovolOneH lam 𝓖) →
  ∃ (dx : Measure (Fin r → Fin V.rank → AE D)) (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)),
    SdW D.host.F D.host.E D.sp.cm.sig V.rank V.gram (AF D.host.F) ψ r dx ∧
    SdHerm D.host.F D.host.E D.sp.cm.sig (AF D.host.F) ψ r db ∧
    ∀ (φ : Mx D V.rank r → ℂ) (β : HermE D r),
      W ψ V μ lam φ β = coefN D.sp.cm.sig V.gram ψ dx db (fun X => φ (tupOf X)) β.1 := by
  rintro D r V ψ hψ μ ⟨𝓕, hμ⟩ lam ⟨𝓖, hl⟩
  refine ⟨μ.map tupInv, lam.map hermTo, sdW_map V hψ hμ, sdHerm_map hψ hl,
    fun φ β => ?_⟩
  obtain ⟨i1, -, i3, -, -, -⟩ := lattice_Mx D r r
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : IsTopologicalAddGroup (Mx D V.rank r) := k1
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  haveI : IsTopologicalAddGroup (Matrix (Fin r) (Fin r) (AE D)) := i1
  haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig r) := ⟨rfl⟩
  haveI : BorelSpace (Fin r → Fin V.rank → AE D) := borel_tup
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  unfold W coefN
  rw [integral_map_of (hermTo (D := D) (r := r)) hermFrom hermFrom_hermTo hermTo_hermFrom hermTo_add continuous_hermTo continuous_hermFrom]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hstar : starN D.sp.cm.sig V.gram ψ (μ.map tupInv) (fun X => φ (tupOf X)) (hermTo b) = Jt ψ V μ φ b := by
    unfold starN Jt
    rw [integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hg : gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y) =
        GlobalTheory.StdUnn.inner V y y := by
      ext a c
      exact hR_tup V y y a c
    change φ y * ψ (_ * Algebra.trace _ _ (Matrix.trace (b.1 * gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y)))) = _
    rw [hg]
    rfl
  change _ = starN D.sp.cm.sig V.gram ψ _ _ (hermTo b) * _
  rw [hstar]
  rfl

end GlobalTheory.CompanionTheory.SiegelND
