import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.ContinuousFrameUM
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.CountableProdSub
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SectionSumIntegralExpand
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FirstChernHodgeTateFacts

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {R : RD d} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem fix_mul {x y : d.G}
    (hx : ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (hy : ∀ k, inFrame d.b y k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (k) : inFrame d.b (x * y) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp only [hy]
  rw [← Matrix.mul_apply, Matrix.mul_one, hx]

theorem perF (h : Hyp L nb uM nb' w₁ cM δ) (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * th T (γ + β) = Ψ (nb β * (uM u * x)) * th T β := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (fix_nb h γ)]
  congr 1
  unfold th
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]

theorem perFE (h : Hyp L nb uM nb' w₁ cM δ) (Ψ : d.G → ℝ≥0∞) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * ‖th T (γ + β)‖ₑ = Ψ (nb β * (uM u * x)) * ‖th T β‖ₑ := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (fix_nb h γ)]
  congr 2
  unfold th
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]

theorem shift_eq (h : Hyp L nb uM nb' w₁ cM δ) (r b u : Fin L.n → AE F E) (s a : AF F) :
    sM R L (r + b) * cM (u, s + a) = (sM R L r * cM (0, s)) * (sM R L b * cM (u, a)) := by
  have e1 : cM (u, s + a) = cM (0, s) * cM (u, a) := by
    rw [cM_split h, centre_matrix_add h, cM_split h u a, ← mul_assoc, cM_comm h, mul_assoc]
  rw [sM_add, e1]
  simp only [mul_assoc]
  rw [← mul_assoc (sM R L b) (cM (0, s)), siegel_centre_commute h, mul_assoc]

theorem rr_rat (h : Hyp L nb uM nb' w₁ cM δ) {r : Fin L.n → AE F E} (hr : r ∈ L.ratV) {s : AF F}
    (hs : s ∈ (algebraMap F (AF F)).range) : sM R L r * cM (0, s) ∈ rat2 σ d.Y :=
  mul_mem (sM_rat hr) (cM_rat h (c := (0, s)) (zero_mem _) hs)

theorem rr_fix (h : Hyp L nb uM nb' w₁ cM δ) (r : Fin L.n → AE F E) (s : AF F) (k) :
    inFrame d.b (sM R L r * cM (0, s)) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) :=
  fix_mul (L := L) (fix_sM r) (fix_cM h (0, s)) k

theorem pt_eq (h : Hyp L nb uM nb' w₁ cM δ) (x : d.G) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb β * (uM u * x) = sM R L (pb L β + (tau L uM nb' δ (u, C4.prj L β)).1) *
      (cM (u, pa L δ β + (tau L uM nb' δ (u, C4.prj L β)).2) * (L.j (nb' (C4.prj L β)) * x)) := by
  calc nb β * (uM u * x) = (L.j (nb' (C4.prj L β)) * (sM R L (pb L β) * cM (u, pa L δ β))) * x := by
        rw [nb_split (R := R) h β]
        simp only [mul_assoc]
        rw [← mul_assoc (cM (0, pa L δ β)) (uM u), ← cM_comm h, ← cM_split h]
    _ = _ := by rw [move h]; simp only [mul_assoc]

instance countable_ratV (L : LD d) : Countable L.ratV := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have h : ((L.ratV : AddSubgroup (Fin L.n → AE F E)) : Set (Fin L.n → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _)).mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := C1.ratV_inc hu
    exact ⟨v, rfl⟩
  exact h.to_subtype

theorem coordsC_ck (h : Hyp L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((pb L β, pa L δ β), C4.prj L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * th T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * th' T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := pEquiv h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((pb L β, pa L δ β), C4.prj L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainC (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (continuous_tau h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * th T p.2)
    (fun q => Ψ (sM R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * th' T' q.1)
    (fun γ hγ u β => perF h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (sM R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (sM R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, shift_eq h, mul_assoc (sM R L g.1 * cM (0, g.2)), hΨ _ (rr_rat h hg1 hg2) (rr_fix h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * th T β = Ψ (sM R L (pb L β + (tau L uM nb' δ (u, C4.prj L β)).1) *
        (cM (u, pa L δ β + (tau L uM nb' δ (u, C4.prj L β)).2) * (L.j (nb' (C4.prj L β)) * x))) * th' T' (C4.prj L β)
      rw [pt_eq (R := R) h x u β]
      congr 1
      unfold th th'
      rw [C4.tr_sub L hT β])
  rw [key, ← Measure.prod_restrict]

theorem coordsE_ck (h : Hyp L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((pb L β, pa L δ β), C4.prj L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖th T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (sM R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖th' T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := pEquiv h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((pb L β, pa L δ β), C4.prj L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainE (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (continuous_tau h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * ‖th T p.2‖ₑ)
    (fun q => Ψ (sM R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * ‖th' T' q.1‖ₑ)
    (fun γ hγ u β => perFE h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (sM R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (sM R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, shift_eq h, mul_assoc (sM R L g.1 * cM (0, g.2)), hΨ _ (rr_rat h hg1 hg2) (rr_fix h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * ‖th T β‖ₑ = Ψ (sM R L (pb L β + (tau L uM nb' δ (u, C4.prj L β)).1) *
        (cM (u, pa L δ β + (tau L uM nb' δ (u, C4.prj L β)).2) * (L.j (nb' (C4.prj L β)) * x))) * ‖th' T' (C4.prj L β)‖ₑ
      rw [pt_eq (R := R) h x u β]
      congr 2
      unfold th th'
      rw [C4.tr_sub L hT β])
  rw [key, ← Measure.prod_restrict]

end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

end
