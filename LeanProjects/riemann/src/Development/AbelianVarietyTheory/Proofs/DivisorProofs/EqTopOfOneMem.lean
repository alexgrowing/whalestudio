import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetIffMaximalLevelCongruentConjIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise
open scoped nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

variable {D : D7}

theorem star_eq (x : D.host.E) : star x = D.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj D.host x

theorem smul_finRat (S T : HSp D) (s : D.host.E) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    incA D s • GlobalTheory.VacUnique.finRat S T γ = GlobalTheory.VacUnique.finRat S T (s • γ) := by
  ext i j
  change incA D s * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] γ i j) = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (s * γ i j)
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] s) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

section Lat

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem mem_latRat_iff (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS) (hLT : IsStdLat LT)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    γ ∈ GlobalTheory.LatVac.latRat S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) ↔
      ∀ i j, γ i j ∈ D.host.AA0 := by
  rw [← GlobalTheory.AdForm.RatLat.AA_eq hcc]
  have hg : ∀ (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) i j,
      GlobalTheory.LatVac.genMap S T a s t i j = a * t i * star (s j) := fun a s t i j => by
    simp [GlobalTheory.LatVac.genMap, gS, Matrix.one_apply]
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      obtain ⟨b, hb⟩ := (hLS s).1 hs j
      obtain ⟨b', hb'⟩ := (hLT t).1 ht i
      have e : a * t i * star (s j) = (b' * D.host.conj • b : 𝓞 D.host.E) • a := by
        rw [← hb, ← hb', star_eq]
        change a * (b' : D.host.E) * D.host.conj (b : D.host.E) = ((b' : D.host.E) * D.host.conj (b : D.host.E)) * a
        ring
      rw [hg, e]
      exact (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem _ ha
    | zero => exact fun i j => D.host.AA.zero_mem
    | add x y _ _ hx hy => exact fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).add_mem (hx i j) (hy i j)
    | neg x _ hx => exact fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).neg_mem (hx i j)
  · intro h
    rw [Matrix.matrix_eq_sum_single γ]
    refine sum_mem fun i _ => sum_mem fun j _ => AddSubgroup.subset_closure
      ⟨γ i j, h i j, Pi.single j 1, (hLS _).2 fun k => ?_, Pi.single i 1, (hLT _).2 fun k => ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs
      exacts [⟨1, rfl⟩, ⟨0, rfl⟩]
    · rw [Pi.single_apply]
      split_ifs
      exacts [⟨1, rfl⟩, ⟨0, rfl⟩]
    · refine Matrix.ext fun k l => ?_
      rw [hg, Matrix.single_apply, Pi.single_apply, Pi.single_apply]
      by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2, eq_comm (a := k), eq_comm (a := l)]

theorem finRat_mem_iff (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.VacUnique.finRat S T γ ∈ latO S T LS LT (fun _ => True) ↔ γ ∈ YYl D (stdL D S.rank) (stdL D T.rank) := by
  rw [GlobalTheory.OddGenus.mem_iff_entries, ← mem_latRat_iff hcc gS hLS hLT]
  exact GlobalTheory.AdForm.RatLat.finTens_mem_iff hψ hS hT γ

theorem half_mem_iff (hcc : D.host.ccK = ⊤) (hLS : IsStdLat LS) (hLT : IsStdLat LT) (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P) (t : WO S T)
    (ht : IsHalf (cA D e) t) :
    t ∈ latO S T LS LT (fun _ => True) ↔ ∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have fr : ∀ {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}, IsStdLat L →
      Formalism.L2.DIV.IsFrame (1 : GL (Fin n) (EAf D)) L := fun {n L} h => by
    have e : L = Formalism.UG.stdLat (n := Fin n) (A := D.host.E) (𝓞 D.host.E) := by
      ext y
      rw [h, Formalism.UG.stdLat, Submodule.mem_pi]
      exact ⟨fun H i _ => H i, fun H i => H i trivial⟩
    exact e ▸ Formalism.L2.DIV.frame_standard D.host.F D.host.E n
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T LS LT 1 1 hS hT (fr hLS) (fr hLT) _ _
    (GlobalTheory.RefDatumLev.isIdemSum_conjPl he.1) ?_ t ht]
  · simp only [IsIntM, frMapO, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, Matrix.map_apply]
  · intro Q hQ h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hQ
    rw [hcc, Ideal.absNorm_top, mul_one] at h
    have h' : Formalism.L2.DIV.starOHom ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := h
    rw [map_natCast] at h'
    refine he.2 w hw ?_
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h'

theorem approx (hψ : IsStdChar D ψ (-1)) (hcc : D.host.ccK = ⊤) (gS : S.gram = 1) (hLS : IsStdLat LS)
    (hLT : IsStdLat LT) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {k : ℕ} (hk : 0 < k) {u : WO S T}
    (hu : u ∈ latO S T LS LT (fun _ => True)) :
    ∃ γ ∈ YYl D (stdL D S.rank) (stdL D T.rank), ∃ v ∈ latO S T LS LT (fun _ => True),
      u = GlobalTheory.VacUnique.finRat S T γ + k • v := by
  have hi := GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  obtain ⟨ρ, ⟨M, rfl⟩, v, hv, h⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).2.1
    (incA D (k : D.host.E)⁻¹ • u) (Matrix.ext fun i j => by
      have : infPart D (u i j) = 0 := congrFun (congrFun hi i) j
      change infPart D (incA D (k : D.host.E)⁻¹ * u i j) = 0
      rw [RingHom.map_mul, this, mul_zero])
  have hv' := GlobalTheory.VacUnique.latO_inf S T _ _ _ hv
  have e1 : incA D (k : D.host.E)⁻¹ • u = GlobalTheory.VacUnique.finRat S T M + v := by
    refine GlobalTheory.AdForm.RatLat.eq_of_parts (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_)
    · have h1 : infPart D (u i j) = 0 := congrFun (congrFun hi i) j
      have h2 : infPart D (v i j) = 0 := congrFun (congrFun hv' i) j
      have h3 : infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
      change infPart D (incA D (k : D.host.E)⁻¹ * u i j) = infPart D (GlobalTheory.VacUnique.finRat S T M i j + v i j)
      rw [RingHom.map_mul, RingHom.map_add, h1, h2, h3, mul_zero, add_zero]
    · have h1 : finPart D (incA D (k : D.host.E)⁻¹ * u i j - incA D (M i j) - v i j) = 0 := congrFun (congrFun h i) j
      have h3 : finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := rfl
      change finPart D (incA D (k : D.host.E)⁻¹ * u i j) = finPart D (GlobalTheory.VacUnique.finRat S T M i j + v i j)
      rw [RingHom.map_sub, RingHom.map_sub, sub_sub, sub_eq_zero] at h1
      rw [RingHom.map_add, h3, h1]
  have e2 : u = GlobalTheory.VacUnique.finRat S T (k • M) + k • v := by
    rw [map_nsmul, ← smul_add, ← e1, smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hk]
  refine ⟨k • M, (finRat_mem_iff hψ hcc gS hLS hLT hS hT _).1 ?_, v, hv, e2⟩
  rw [← sub_eq_iff_eq_add] at e2
  rw [← e2]
  exact sub_mem hu (nsmul_mem hv k)

end Lat

theorem smul_mem_skew (I : Ideal (𝓞 D.host.E)) {a d : ℕ} {s : D.host.E}
    (hs : s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))))
    {γ : Matrix (Fin d) (Fin a) D.host.E} (hγ : γ ∈ YYl D (stdL D a) (stdL D d)) :
    s • γ ∈ YYl D (stdL D a) (skewLat D I d) := by
  induction hγ using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA, rfl⟩ := hB
    refine Submodule.subset_span ⟨c, hc, s • A, ?_, smul_comm _ _ _⟩
    clear hc
    induction hA using Submodule.span_induction with
    | mem A hA =>
      refine Submodule.subset_span fun x hx i _ => ?_
      obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hA x hx i trivial)
      rw [Matrix.smul_mulVec, Pi.smul_apply, ← hb, smul_eq_mul, mul_comm]
      exact Submodule.smul_mem _ b hs
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem skew_mem_closure (I : Ideal (𝓞 D.host.E)) {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : z ∈ YYl D (stdL D a) (skewLat D I d)) :
    z ∈ AddSubgroup.closure {w : Matrix (Fin d) (Fin a) D.host.E |
      ∃ s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))),
        ∃ γ ∈ YYl D (stdL D a) (stdL D d), w = s • γ} := by
  have hA : ∀ A ∈ homL D (stdL D a) (skewLat D I d), ∀ i j,
      A i j ∈ (((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      intro i j
      have := hA (Pi.single j 1) (fun k _ => by
        rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨1, rfl⟩, zero_mem _]) i trivial
      rwa [Matrix.mulVec_single_one] at this
    | zero => exact fun i j => zero_mem _
    | add x y _ _ hx hy => exact fun i j => add_mem (hx i j) (hy i j)
    | smul c x _ hx => exact fun i j => Submodule.smul_mem _ c (hx i j)
  suffices h : ∀ r : 𝓞 D.host.E, r • z ∈ AddSubgroup.closure {w : Matrix (Fin d) (Fin a) D.host.E |
      ∃ s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))),
        ∃ γ ∈ YYl D (stdL D a) (stdL D d), w = s • γ} by simpa using h 1
  induction hz using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA', rfl⟩ := hB
    intro r
    rw [Matrix.matrix_eq_sum_single (r • c • A)]
    refine sum_mem fun i _ => sum_mem fun j _ => AddSubgroup.subset_closure
      ⟨A i j, hA A hA' i j, Matrix.single i j (r • c), (GlobalTheory.OddGenus.mem_iff_entries D a d _).2 fun k l => ?_, ?_⟩
    · rw [Matrix.single_apply]
      split_ifs
      · exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem r hc
      · exact D.host.AA0.zero_mem
    · rw [Matrix.smul_single, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_smul_comm, mul_comm]
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; rw [smul_add]; exact add_mem (hx r) (hy r)
  | smul c x _ hx => intro r; rw [smul_smul]; exact hx _

theorem mul_mem_of_skew {I : Ideal (𝓞 D.host.E)} (hI : D.host.conj • I ≠ ⊥) {s : D.host.E}
    (hs : s ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (D.host.conj • I : Ideal (𝓞 D.host.E))))
    {m : 𝓞 D.host.E} (hm : m ∈ D.host.conj • I) : ∃ b ∈ I, (b : D.host.E) = m * s := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hI)] at hs
  obtain ⟨b, hb, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hs _ (FractionalIdeal.mem_coeIdeal_of_mem _ hm))
  exact ⟨b, hb, e.trans (mul_comm _ _)⟩

theorem smul_skew_mem {I : Ideal (𝓞 D.host.E)} (hI : D.host.conj • I ≠ ⊥) {a d : ℕ} {z : Matrix (Fin d) (Fin a) D.host.E}
    (hz : z ∈ YYl D (stdL D a) (skewLat D I d)) {m : 𝓞 D.host.E} (hm : m ∈ D.host.conj • I) :
    (m : D.host.E) • z ∈ YYl D (stdL D a) (stdL D d) := by
  have h := skew_mem_closure I hz
  clear hz
  induction h using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨s, hs, γ, hγ, rfl⟩ := hw
    obtain ⟨b, -, e⟩ := mul_mem_of_skew hI hs hm
    rw [smul_smul, ← e]
    exact Submodule.smul_mem _ b hγ
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem conj_mul_conj : D.host.conj * D.host.conj = 1 :=
  AlgEquiv.ext fun x => by
    change D.host.conj (D.host.conj x) = x
    rw [← star_eq, ← star_eq, star_star]

theorem conj_conj_smul (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  rw [smul_smul, conj_mul_conj, one_smul]

theorem mem_conj_smul {I : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} : b ∈ D.host.conj • I ↔ D.host.conj • b ∈ I := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_eq_of_mul_eq_one_right conj_mul_conj]

theorem cA_incA_int (b : 𝓞 D.host.E) :
    cA D (incA D (b : D.host.E)) = incA D ((D.host.conj • b : 𝓞 D.host.E) : D.host.E) := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_eq]
  rfl

theorem modul_ne_bot (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : modul P c ≠ ⊥ :=
  Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

theorem exists_add_two {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : GoodIdem e P)
    (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : ∃ m ∈ modul P c, ∃ u : 𝓞 D.host.E, m + u * 2 = 1 := by
  have h : IsCoprime (modul P c) (Ideal.span {2}) := IsCoprime.prod_left fun w hw => IsCoprime.pow_left (by
    rw [Ideal.isCoprime_iff_sup_eq]
    refine w.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => he.2 w hw ?_)
    have h2 : (2 : 𝓞 D.host.E) ∈ w.asIdeal := h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    obtain ⟨k, hk⟩ := D.host.two_dvd_QS
    rw [hk, mul_assoc, mul_assoc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h2)
  obtain ⟨m, hm, t, ht, e⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
  exact ⟨m, hm, u, e⟩

theorem eq_top_of_one_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {I : Ideal (𝓞 E)}
    (hI : I ≠ ⊥) (h : (1 : Formalism.L2.Herm.intAf F E) ∈ Formalism.L2.DIV.idS F I) : I = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]
  apply Formalism.L2.DIV.cmpS_inj (F := F) I hI
  rw [map_one, map_one, map_zero, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact h

theorem isCoprime_conj {e : Formalism.L2.Theta.AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    (c : Formalism.L2.DIV.Pl D.host.E → ℕ) : IsCoprime (D.host.conj • modul P c) (modul P c) := by
  obtain ⟨-, h1, t, ht, h2⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e P c he
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (1 - cA D e)) := by
    rw [CosetCong.inId_iff, map_sub, map_one]
    exact (CosetCong.conj_idem c he).2
  obtain ⟨h4, h5⟩ := h3
  have h6 : (1 : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
      Formalism.L2.DIV.idS D.host.F (D.host.conj • modul P c ⊔ modul P c) := by
    have e1 : (1 : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D e, h1⟩ * ⟨_, h4⟩ + t := by
      apply Subtype.ext
      change (1 : EAf D) = toEAf D e * toEAf D (1 - cA D e) + (t : EAf D)
      rw [h2, ← RingHom.map_mul, mul_sub, he.2, mul_one, sub_zero, add_sub_cancel]
    rw [e1]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.map_mono le_sup_left h5)) (Ideal.map_mono le_sup_right ht)
  exact Ideal.isCoprime_iff_sup_eq.2
    (eq_top_of_one_mem (fun h => modul_ne_bot P c (le_bot_iff.1 (le_sup_right.trans h.le))) h6)

theorem toEAf_surj : Function.Surjective (toEAf D) := fun z => by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul a α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] a, rfl⟩
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, RingHom.map_add _ _ _⟩

theorem half_ext {S T : HSp D} {a : Formalism.L2.Theta.AE D} (ha : infPart D a = 0) {x y : WO S T} (hx : IsHalf a x) (hy : IsHalf a y)
    (h : ∀ i j, toEAf D (x i j) = toEAf D (y i j)) : x = y := by
  refine GlobalTheory.AdForm.RatLat.eq_of_parts (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_)
  · change infPart D (x i j) = infPart D (y i j)
    rw [← hx, ← hy, RingHom.map_mul, RingHom.map_mul, ha, zero_mul, zero_mul]
  · exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (h i j)

theorem inId_mul {I : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I) {x : Formalism.L2.Theta.AE D}
    (hx : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (incA D (b : D.host.E) * x)) := by
  have h1 : Formalism.L2.DIV.oToS D.host.F D.host.E b * ⟨_, hx⟩ ∈ Formalism.L2.DIV.idS D.host.F I :=
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
  rw [RingHom.map_mul]
  exact ⟨mul_mem (Formalism.L2.DIV.oToS D.host.F D.host.E b).2 hx, h1⟩

theorem inId_add {I : Ideal (𝓞 D.host.E)} {x y : EAf D} (hx : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I y) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  exact ⟨add_mem h1 h3, add_mem h2 h4⟩

end GlobalTheory.SkewLevel

end
