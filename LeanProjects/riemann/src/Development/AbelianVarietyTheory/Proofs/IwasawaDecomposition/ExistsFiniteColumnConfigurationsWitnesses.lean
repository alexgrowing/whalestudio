import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameCfgRefl
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld

open Formalism.L2.DIV

theorem norm_piG_le {P : Pre} (px : PreX P) (i : Fin 2) (φ : P.host.E →+* ℂ) :
    ‖φ (px.piG i : P.host.E)‖ ≤ (P.host.g i : ℝ) + 1 := by
  have h := congrArg φ (px.piG_norm i)
  have hc : φ (P.host.conj (px.piG i : P.host.E)) = starRingEnd ℂ (φ (px.piG i : P.host.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
  rw [map_mul, hc, map_natCast, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h2 : ‖φ (px.piG i : P.host.E)‖ ^ 2 = (P.host.g i : ℝ) := by exact_mod_cast h
  nlinarith [sq_nonneg (‖φ (px.piG i : P.host.E)‖ - 1), norm_nonneg (φ (px.piG i : P.host.E))]

theorem finite_piG (P : Pre) :
    {g : Fin 2 → 𝓞 P.host.E | ∀ i (φ : P.host.E →+* ℂ), ‖φ (g i : P.host.E)‖ ≤ (P.host.g i : ℝ) + 1}.Finite := by
  refine (Set.Finite.pi (t := fun i => ((↑) : 𝓞 P.host.E → P.host.E) ⁻¹'
    {x | IsIntegral ℤ x ∧ ∀ φ : P.host.E →+* ℂ, ‖φ x‖ ≤ (P.host.g i : ℝ) + 1}) fun i =>
      (NumberField.Embeddings.finite_of_norm_le P.host.E ℂ _).preimage
        RingOfIntegers.coe_injective.injOn).subset ?_
  intro g hg i _
  exact ⟨RingOfIntegers.isIntegral_coe _, hg i⟩

open Classical in

def chiOf {P : Pre} (f : Top.Fr P) : Fin P.R.m → HeightOneSpectrum (𝓞 P.host.E) → 𝓞 P.host.E → ℂ :=
  fun j w y => if h : (f.P.Div 0 w ∨ f.P.Div 1 w) ∧ (y : P.host.E) ≠ 0 ∧ IsUnit (Ideal.Quotient.mk w.asIdeal y) then
    ((((f.mu0 j).locK w (Units.mk0 (y : P.host.E) h.2.1))⁻¹ : ℂˣ) : ℂ) else 0

theorem chiC_eq {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (h : I.Ok) : chiC I = chiOf I.C := by
  classical
  funext j w y
  have hv : w ∈ (B.primes px).vGs ↔ (I.C.P.Div 0 w ∨ I.C.P.Div 1 w) := by
    rw [← h.pibar 0 w, ← h.pibar 1 w]
    simp [Formalism.L2.Col.Primes.vGs]
  unfold chiC chiOf
  by_cases hw : w ∈ (B.primes px).vGs
  · by_cases hu : IsUnit (Ideal.Quotient.mk w.asIdeal y)
    · have hy : (y : B.host.E) ≠ 0 := by
        intro h0
        have hy0 : y = 0 := RingOfIntegers.coe_injective (by simpa using h0)
        subst hy0
        haveI : w.asIdeal.IsPrime := w.isPrime
        exact hu.ne_zero (map_zero _)
      rw [dif_pos hw, dif_pos hu, dif_pos ⟨hv.1 hw, hy, hu⟩]
      have ht := (h.ch_tied.mu0 j).atg ⟨w, hw⟩ (Units.mk0 _ hy) y hu.unit rfl (by simp)
      rw [Units.val_inv_eq_inv_val, ht, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
    · rw [dif_pos hw, dif_neg hu, dif_neg (fun h' => hu h'.2.2)]
  · rw [dif_neg hw, dif_neg (fun h' => hw (hv.2 h'.1))]

def ramPl {P : Pre} (ξ : Formalism.L2.Host.HChar P.host.E) : Set (HeightOneSpectrum (𝓞 P.host.F)) :=
  {v | ∃ a : Neutral.B1.Ideles P.host.E, Col2.finAf P.host.F P.host.E a ∈ inertAt P.host.E v ∧ ξ.1 a ≠ 1}

theorem qprime_eq_of_reads {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K]
    {σ : K →+* ℂ} {μ : Chr F E K} {ξ : Formalism.L2.Host.HChar E} (h : Col2.Reads σ μ ξ) :
    Qprime μ = {v | ∃ a : Neutral.B1.Ideles E, Col2.finAf F E a ∈ inertAt E v ∧ ξ.1 a ≠ 1} := by
  ext v
  simp only [Qprime, Set.mem_setOf_eq, SetLike.not_le_iff_exists, MonoidHom.mem_ker]
  constructor
  · rintro ⟨y, hy, hne⟩
    obtain ⟨a, rfl⟩ := Col2.finAf_surjective F E y
    refine ⟨a, hy, fun h1 => hne (Units.ext (σ.injective ?_))⟩
    rw [← h a, h1]
    simp
  · rintro ⟨a, ha, hne⟩
    refine ⟨_, ha, fun h1 => hne (Units.ext ?_)⟩
    rw [h a, h1]
    simp

open Classical in

def qBound {P : Pre} (ξ : Formalism.L2.Host.HChar P.host.E) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  if (ramPl ξ).Finite then {Q | ∃ v ∈ ramPl ξ, Ideal.under (𝓞 P.host.F) Q.asIdeal = v.asIdeal} else ∅

theorem finite_qBound {P : Pre} (ξ : Formalism.L2.Host.HChar P.host.E) : (qBound ξ).Finite := by
  classical
  unfold qBound
  split_ifs with hf
  · refine (hf.biUnion fun v _ => Ideal.finite_factors
      (I := Ideal.map (algebraMap (𝓞 P.host.F) (𝓞 P.host.E)) v.asIdeal) ?_).subset ?_
    · rw [Ideal.zero_eq_bot, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
      exact v.ne_bot
    · rintro Q ⟨v, hv, hQ⟩
      refine Set.mem_biUnion hv ?_
      show Q.asIdeal ∣ _
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
      exact hQ.ge
  · exact Set.finite_empty

theorem qC_subset {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (h : I.Ok) (ξ : Formalism.L2.Host.HChar B.host.E) :
    (↑(qC I ξ) : Set (HeightOneSpectrum (𝓞 B.host.E))) ⊆ qBound (P := B.toPre) ξ := by
  classical
  unfold qC
  split_ifs with hx
  · have hr : Qprime (I.tup hx.choose : Chr B.fields.F B.fields.E B.fields.K) = ramPl (P := B.toPre) ξ := by
      have := qprime_eq_of_reads (h.xi_reads hx.choose)
      rw [hx.choose_spec] at this
      exact this
    intro Q hQ
    have hQ' : Q ∈ Formalism.L2.Col.QE I.sel (I.tup hx.choose : Chr B.fields.F B.fields.E B.fields.K) := hQ
    unfold Formalism.L2.Col.QE at hQ'
    split_ifs at hQ' with hfin
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ'
      rw [Set.Finite.mem_toFinset] at hv
      unfold qBound
      rw [if_pos (hr ▸ hfin)]
      exact ⟨v, hr ▸ hv, h.sel_ok v⟩
    · simp at hQ'
  · simp

theorem qC_of_not_mem {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) {ξ : Formalism.L2.Host.HChar B.host.E}
    (hξ : ξ ∉ Set.range I.xi) : qC I ξ = ∅ := by
  classical
  unfold qC
  rw [dif_neg fun ⟨a, ha⟩ => hξ ⟨a, ha⟩]

theorem finite_qFns {P : Pre} {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (hΞ : Ξ.Finite) :
    {q : Formalism.L2.Host.HChar P.host.E → Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (∀ ξ, (↑(q ξ) : Set (HeightOneSpectrum (𝓞 P.host.E))) ⊆ qBound ξ) ∧ ∀ ξ ∉ Ξ, q ξ = ∅}.Finite := by
  classical
  haveI := hΞ.to_subtype
  refine Set.Finite.of_finite_image (f := fun q (ξ : Ξ) => q ξ) ?_ ?_
  · refine (Set.Finite.pi (t := fun ξ : Ξ => {s : Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (↑s : Set (HeightOneSpectrum (𝓞 P.host.E))) ⊆ qBound (ξ : Formalism.L2.Host.HChar P.host.E)}) fun ξ =>
        (finite_qBound (ξ : Formalism.L2.Host.HChar P.host.E)).finite_subsets.preimage Finset.coe_injective.injOn).subset ?_
    rintro _ ⟨q, hq, rfl⟩ ξ _
    exact hq.1 ξ
  · intro q hq q' hq' he
    funext ξ
    by_cases hξ : ξ ∈ Ξ
    · exact congrFun he ⟨ξ, hξ⟩
    · rw [hq.2 ξ hξ, hq'.2 ξ hξ]

theorem exists_finite_cfg : ∀ (P : Pre) (f : Top.Fr P) (F F₀ : IntermediateField ℚ ℂ) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)),
  ∃ (n : ℕ) (Wt : Fin n → Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0),
    (∀ i, (Wt i).1.fields.Ok ∧ (Wt i).2.2.Ok) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → B.toPre = P → HEq I.C f → B.KsC = F →
      B.fixedCoefficientFieldInComplex = F₀ → HEq (Set.range I.xi) Ξ → ∃ i, GlobalTheory.Mem.HFld.SameCfg B px I (Wt i).1 (Wt i).2.1 (Wt i).2.2 := by
  intro P f F F₀ Ξ
  classical
  let admitted : (Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0) → Prop := fun x =>
    x.1.fields.Ok ∧ x.2.2.Ok ∧ x.1.toPre = P ∧ HEq x.2.2.C f ∧ x.1.KsC = F ∧ x.1.fixedCoefficientFieldInComplex = F₀ ∧ HEq (Set.range x.2.2.xi) Ξ
  let Tr : Type := (Fin 2 → 𝓞 P.host.E) × (Fin P.R.m → HeightOneSpectrum (𝓞 P.host.E) → 𝓞 P.host.E → ℂ) ×
    (Formalism.L2.Host.HChar P.host.E → Finset (HeightOneSpectrum (𝓞 P.host.E)))
  let T : Set Tr := {t | ∃ x, admitted x ∧ HEq x.2.1.piG t.1 ∧ HEq (chiC x.2.2) t.2.1 ∧ HEq (qC x.2.2) t.2.2}
  have hT : T.Finite := by
    by_cases hΞ : Ξ.Finite
    · refine ((finite_piG P).prod ((Set.finite_singleton (chiOf f)).prod (finite_qFns hΞ))).subset ?_
      rintro ⟨t1, t2, t3⟩ ⟨⟨B, px, I⟩, ⟨-, hI, hP, hC, -, -, hX⟩, h1, h2, h3⟩
      dsimp only at hI hP hC hX h1 h2 h3
      subst hP
      cases eq_of_heq hC
      cases eq_of_heq hX
      cases eq_of_heq h1
      cases eq_of_heq h2
      cases eq_of_heq h3
      refine ⟨fun i φ => norm_piG_le px i φ, chiC_eq I hI, fun ξ => qC_subset I hI ξ, fun ξ hξ => qC_of_not_mem I hξ⟩
    · convert Set.finite_empty
      ext ⟨t1, t2, t3⟩
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨B, px, I⟩, ⟨-, -, hP, -, -, -, hX⟩, -⟩
      dsimp only at hP hX
      subst hP
      exact hΞ (eq_of_heq hX ▸ Set.finite_range I.xi)
  have hch : ∀ t : T, ∃ x, admitted x ∧ HEq x.2.1.piG t.1.1 ∧ HEq (chiC x.2.2) t.1.2.1 ∧ HEq (qC x.2.2) t.1.2.2 := fun t => t.2
  choose w hwA hwR using hch
  haveI := hT.fintype
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun i => w (e.symm i), fun i => ⟨(hwA _).1, (hwA _).2.1⟩, ?_⟩
  intro B px I hBo hIo hP hC hK hL hX
  have hx : admitted ⟨B, px, I⟩ := ⟨hBo, hIo, hP, hC, hK, hL, hX⟩
  subst hP
  have ht : ((px.piG, chiC I, qC I) : Tr) ∈ T := ⟨⟨B, px, I⟩, hx, HEq.rfl, HEq.rfl, HEq.rfl⟩
  refine ⟨e ⟨_, ht⟩, ?_⟩
  have key : ∀ s : T, s = ⟨_, ht⟩ → GlobalTheory.Mem.HFld.SameCfg B px I (w s).1 (w s).2.1 (w s).2.2 := by
    rintro s rfl
    obtain ⟨-, -, h3, h4, -, -, h6⟩ := hwA ⟨_, ht⟩
    obtain ⟨r1, r2, r3⟩ := hwR ⟨_, ht⟩
    exact ⟨h3.symm, hC.trans h4.symm, hX.trans h6.symm, r1.symm, r2.symm, r3.symm⟩
  exact key _ (e.symm_apply_apply _)

end GlobalTheory.Mem.HFld

end
