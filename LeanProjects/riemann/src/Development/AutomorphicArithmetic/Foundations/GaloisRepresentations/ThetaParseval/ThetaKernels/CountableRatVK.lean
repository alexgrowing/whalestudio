import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.CountableRatV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HandsCoordkTau
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitSectionIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LamMapK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzEqFlatK

set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem fix_mul_k {x y : d.G}
    (hx : ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (hy : ∀ k, inFrame d.b y k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (k) : inFrame d.b (x * y) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp only [hy]
  rw [← Matrix.mul_apply, Matrix.mul_one, hx]
theorem perF_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T (γ + β) = Ψ (nb β * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_nb_k h γ)]
  congr 1
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem perFE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℝ≥0∞) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T (γ + β)‖ₑ = Ψ (nb β * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β‖ₑ := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_nb_k h γ)]
  congr 2
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem shift_eq_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (r b u : Fin L.n → AE F E) (s a : AF F) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (r + b) * cM (u, s + a) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) := by
  have e1 : cM (u, s + a) = cM (0, s) * cM (u, a) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.centre_additive h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h u a, ← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_comm_k h, mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_add_k, e1]
  simp only [mul_assoc]
  rw [← mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b) (cM (0, s)), _root_.PositivityTheory.SiegelWeilFormula.Act.C5.unipotent_commutes_centre h, mul_assoc]
theorem rr_rat_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {r : Fin L.n → AE F E} (hr : r ∈ L.ratV) {s : AF F}
    (hs : s ∈ (algebraMap F (AF F)).range) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s) ∈ rat2 σ d.Y :=
  mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_rat_k hr) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_rat_k h (c := (0, s)) (zero_mem _) hs)
theorem rr_fix_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (r : Fin L.n → AE F E) (s : AF F) (k) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s)) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.fix_mul_k (L := L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_sM_k r) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_cM_k h (0, s)) k
theorem pt_eq_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (x : d.G) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb β * (uM u * x) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
      (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x)) := by
  calc nb β * (uM u * x) = (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β) * cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β))) * x := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nb_split_k (R := R) h β]
        simp only [mul_assoc]
        rw [← mul_assoc (cM (0, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β)) (uM u), ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_comm_k h, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h]
    _ = _ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.move_k h]; simp only [mul_assoc]
instance countable_ratV_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Countable L.ratV := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have h : ((L.ratV : AddSubgroup (Fin L.n → AE F E)) : Set (Fin L.n → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _)).mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
    exact ⟨v, rfl⟩
  exact h.to_subtype
theorem coordsC_ck_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainC (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2)
    (fun q => Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' q.1)
    (fun γ hγ u β => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.perF_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.shift_eq_k h, mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L g.1 * cM (0, g.2)), hΨ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_rat_k h hg1 hg2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
        (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.pt_eq_k (R := R) h x u β]
      congr 1
      unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
theorem coordsE_ck_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainE (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ)
    (fun q => Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' q.1‖ₑ)
    (fun γ hγ u β => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.perFE_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.shift_eq_k h, mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L g.1 * cM (0, g.2)), hΨ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_rat_k h hg1 hg2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β‖ₑ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
        (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)‖ₑ
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.pt_eq_k (R := R) h x u β]
      congr 2
      unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end
