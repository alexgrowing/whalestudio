import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdempotentInIntegralClosureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.DatSum

variable {D : D7}

theorem partAt_eq_smul {S T : HSp D} (c : AE D) (w : WO S T) : partAt c w = c • w := rfl

theorem actO_partAt (S T : HSp D) (g : GA D S) (h : GA D T) (c : AE D) (w : WO S T) :
    actO S T g h (partAt c w) = partAt c (actO S T g h w) := by
  simp only [partAt_eq_smul, actO, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_partAt {S T : HSp D} {c : AE D} (hc : c * c = c) (w : WO S T) : IsHalf c (partAt c w) :=
  fun i j => by simp only [partAt, Matrix.map_apply, ← mul_assoc, hc]

theorem partAt_of_isHalf {S T : HSp D} {c : AE D} {w : WO S T} (h : IsHalf c w) : partAt c w = w :=
  Matrix.ext fun i j => h i j

theorem partAt_add_one_sub {S T : HSp D} (c : AE D) (w : WO S T) : partAt c w + partAt (1 - c) w = w :=
  Matrix.ext fun i j => by simp only [partAt, Matrix.add_apply, Matrix.map_apply]; ring

theorem partAt_neg {S T : HSp D} (c : AE D) (w : WO S T) : partAt c (-w) = -partAt c w := by
  simp only [partAt_eq_smul, smul_neg]

theorem partAt_sub {S T : HSp D} (c : AE D) (w w' : WO S T) : partAt c (w - w') = partAt c w - partAt c w' := by
  simp only [partAt_eq_smul, smul_sub]

theorem finW_add (S T : HSp D) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (y + y') = finW S T y + finW S T y' :=
  Matrix.ext fun a k => by simp [finW, TensorProduct.tmul_add]

theorem finW_neg (S T : HSp D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (-y) = -finW S T y :=
  Matrix.ext fun a k => by simp [finW, TensorProduct.tmul_neg]

theorem finW_sub (S T : HSp D) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (y - y') = finW S T y - finW S T y' := by
  rw [sub_eq_add_neg, finW_add, finW_neg, ← sub_eq_add_neg]

theorem actO_add (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

theorem actO_neg (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (-x) = -actO S T g h x := by
  simp only [actO, Matrix.mul_neg, Matrix.neg_mul]

theorem actO_sub (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x - y) = actO S T g h x - actO S T g h y := by
  rw [sub_eq_add_neg, actO_add, actO_neg, ← sub_eq_add_neg]

theorem frMapAdj_neg (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x := by
  unfold frMapAdj
  simp [Matrix.map_neg, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem partAt_mem_hatA (S T : HSp D) (I : Ideal (𝓞 D.host.E)) (L : Lt D.host.E T.rank) (w : AE D)
    (hw : finPart D w ∈ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ I ∧
      y = a ⊗ₜ[D.host.F] (x : D.host.E)})
    {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) L)) :
    partAt w u ∈ hatA S T (tens (stdL D.host.E S.rank) (I • L)) := by
  let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun u => partAt w u)
    fun x y => Matrix.ext fun i j => mul_add w (x i j) (y i j)
  have main : hatA S T (tens (stdL D.host.E S.rank) L) ≤
      (hatA S T (tens (stdL D.host.E S.rank) (I • L))).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, y, hy, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ WO S T := AddMonoidHom.mk'
      (fun z => Matrix.of fun a k => GlobalTheory.LatticeStable.liftMul D (α ⊗ₜ[D.host.F] y k a) z)
      fun z z' => Matrix.ext fun a k => (GlobalTheory.LatticeStable.liftMul D _).map_add z z'
    have hle : AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ I ∧
        y = a ⊗ₜ[D.host.F] (x : D.host.E)} ≤ (hatA S T (tens (stdL D.host.E S.rank) (I • L))).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, ho, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, (o : D.host.E) • y, ?_, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
        intro k
        have := Submodule.smul_mem_smul ho (hy k)
        exact this
      · ext a k
        change GlobalTheory.LatticeStable.liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] y k a)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul]
        simp [Matrix.smul_apply]
    have e : Ψ (Matrix.of fun a k => pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a) = Φ (finPart D w) :=
      Matrix.ext fun a k => GlobalTheory.LatticeStable.mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hu

end GlobalTheory.LiftLevel.DatSum

noncomputable section

namespace GlobalTheory.LiftLevel.DatSum

variable {D : D7}

def tr (S T : HSp D) (e : AE D) (k₀ : GA D S) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : WO S T :=
  partAt (cA D e) (actO S T k₀ 1 (finW S T y))

theorem tr_eq (S T : HSp D) (e : AE D) (k₀ : GA D S) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    tr S T e k₀ y = actO S T k₀ 1 (partAt (cA D e) (finW S T y)) := (actO_partAt S T k₀ 1 _ _).symm

theorem tr_sub (S T : HSp D) (e : AE D) (k₀ : GA D S) (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    tr S T e k₀ (y - y') = tr S T e k₀ y - tr S T e k₀ y' := by
  simp only [tr, finW_sub, actO_sub, partAt_sub]

theorem tr_neg (S T : HSp D) (e : AE D) (k₀ : GA D S) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    tr S T e k₀ (-y) = -tr S T e k₀ y := by
  simp only [tr, finW_neg, actO_neg, partAt_neg]

theorem intAE_le_top : intAE D ≤ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E,
    x ∈ (⊤ : Ideal (𝓞 D.host.E)) ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)} :=
  (AddSubgroup.closure_le _).2 (by
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, x, Submodule.mem_top, rfl⟩)

theorem tens_inter {n r : ℕ} {I J : Ideal (𝓞 D.host.E)} (h : IsCoprime I J) {L : Lt D.host.E r}
    {y : Matrix (Fin n) (Fin r) D.host.E} (hI : y ∈ tens (stdL D.host.E n) (I • L))
    (hJ : y ∈ tens (stdL D.host.E n) (J • L)) : y ∈ tens (stdL D.host.E n) ((I * J) • L) := by
  rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hI hJ ⊢
  intro k
  rw [Ideal.isCoprime_iff_sup_eq] at h
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ I ⊔ J)
  have e : y k = i • y k + j • y k := by rw [← add_smul, hij, one_smul]
  rw [e]
  refine add_mem ?_ ?_
  · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hi (hJ k)
  · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hj (hI k)

theorem nsmul_mem_hatA (S T : HSp D) {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ 𝔪)
    (L : Lt D.host.E T.rank) {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) L)) :
    N • u ∈ hatA S T (tens (stdL D.host.E S.rank) (𝔪 • L)) := by
  have main : hatA S T (tens (stdL D.host.E S.rank) L) ≤
      (hatA S T (tens (stdL D.host.E S.rank) (𝔪 • L))).comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, N • y, ?_, ?_⟩
    · rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
      intro k
      have := Submodule.smul_mem_smul hN (hy k)
      rwa [Nat.cast_smul_eq_nsmul] at this
    · ext a k
      change N • (pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (N • y k a)
      exact (map_nsmul (TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 α)) N (y k a)).symm
  exact main hu

theorem fullStd (n : ℕ) : (stdL D.host.E n).FG ∧
    Submodule.span D.host.E (stdL D.host.E n : Set (Fin n → D.host.E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [stdL, Submodule.span_span_of_tower]
  convert (Pi.basisFun D.host.E (Fin n)).span_eq
  simp

theorem fullSmul {r : ℕ} {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) {N : Lt D.host.E r}
    (hN : N.FG ∧ Submodule.span D.host.E (N : Set (Fin r → D.host.E)) = ⊤) :
    (𝔞 • N).FG ∧ Submodule.span D.host.E ((𝔞 • N : Lt D.host.E r) : Set (Fin r → D.host.E)) = ⊤ := by
  refine ⟨Submodule.FG.of_le hN.1 Submodule.smul_le_right, ?_⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have h0 : (a : D.host.E) ≠ 0 := by simpa using ha0
  rw [eq_top_iff, ← hN.2, Submodule.span_le]
  exact fun v hv => (Submodule.smul_mem_iff _ h0).1
    (Submodule.subset_span (Submodule.smul_mem_smul ha hv))

theorem omegaK_congr {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)}
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  have hc : (∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1) ↔
      (∀ PP ∈ Pg, LowZero a (y' PP) ∧ topL a (y' PP) = 1) := forall₂_congr fun PP hP => by rw [h PP hP]
  by_cases h1 : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1
  · rw [if_pos h1, if_pos (hc.1 h1)]
  · rw [if_neg h1, if_neg (fun h2 => h1 (hc.2 h2))]

theorem omegaQ_congr {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)}
    (h : ∀ PP ∈ Q, y PP = y' PP) : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
  unfold omegaQ
  have hc : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) := forall₂_congr fun PP hP => by rw [h PP hP]
  by_cases h1 : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dif_pos h1, dif_pos (hc.1 h1)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [show (h1 PP.1 PP.2).2.unit = (hc.1 h1 PP.1 PP.2).2.unit from
      Units.ext (by simp only [IsUnit.unit_spec, h PP.1 PP.2])]
  · rw [dif_neg h1, dif_neg (fun h2 => h1 (hc.2 h2))]

end GlobalTheory.LiftLevel.DatSum

noncomputable section

namespace GlobalTheory.LiftLevel.DatSum

set_option maxHeartbeats 2000000 in
theorem thPDatum_eq_levelSum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → Finite (GlobalTheory.LiftLevel.LvCls C Lv) → (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)))))) → ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL (GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e) (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  intro D S T C hn ΛT hSD hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmov hgen hM Lv h𝔪 hfin hdat x
  show thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : LvCls C Lv,
    Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) *
      indL (liftL S T βS βT Pg Q e) (x + tr S T e k₀ (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))
  have hc : cA D e * cA D e = cA D e := by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hcI := intAE_le_top (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D (cA D e)) (by rw [← map_mul, hc]))
  have hP : ∀ (L : Lt D.host.E T.rank) (u : WO S T), u ∈ hatA S T (tens (stdL D.host.E S.rank) L) →
      partAt (cA D e) u ∈ hatA S T (tens (stdL D.host.E S.rank) L) := by
    intro L u hu
    have := partAt_mem_hatA S T ⊤ L (cA D e) hcI hu
    rwa [Submodule.top_smul] at this
  have hfinW : ∀ (L : Lt D.host.E T.rank) y, y ∈ tens (stdL D.host.E S.rank) L →
      finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) L) :=
    fun L y hy => AddSubgroup.subset_closure ⟨1, fun v => one_mem (v.adicCompletionIntegers D.host.F), y, hy, rfl⟩
  have tmono : ∀ {L L' : Lt D.host.E T.rank}, L ≤ L' →
      tens (stdL D.host.E S.rank) L ≤ tens (stdL D.host.E S.rank) L' := fun h =>
    AddSubgroup.closure_mono (by rintro _ ⟨v, hv, u, hu, rfl⟩; exact ⟨v, hv, u, h hu, rfl⟩)
  have hA1 : (Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ ≤ C.X.Λ := Submodule.smul_le_right
  have hA2 : (Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ ≤ Lv.𝔪 • C.X.Λ :=
    Submodule.smul_mono_left Ideal.mul_le_right
  have hz : ∀ y, IsHalf (cA D e) (partAt (cA D e) (finW S T y)) := fun y => isHalf_partAt hc _
  have hF : ∀ y, frMapAdj S T βS βT (tr S T e k₀ y) = adjA S T βS βT a (partAt (cA D e) (finW S T y)) := by
    intro y; rw [tr_eq]; exact hmov.2.2 _ (hz y)
  have hInt : ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ),
      IsIntM (frMapAdj S T βS βT (tr S T e k₀ y)) := by
    intro y hy; rw [hF]; exact ((hgen _ (hz y)).1).2 (hP _ _ (hfinW _ y (tmono hA1 hy)))
  have hIn2 : ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ),
      tr S T e k₀ y ∈ liftL S T βS βT Pg Q e := by
    intro y hy
    obtain ⟨h1, h3⟩ := (hgen _ (hz y)).2.2 (by rw [← h𝔪]; exact hP _ _ (hfinW _ y (tmono hA2 hy)))
    exact ⟨isHalf_partAt hc _, by rw [hF]; exact h1, fun PP hPP => by rw [hF]; exact h3 PP hPP⟩
  have hcop : IsCoprime (Ideal.span {2} * conjI Lv.𝔪) Lv.𝔪 := IsCoprime.mul_left Lv.odd.symm Lv.cop.symm
  have hfull := GlobalTheory.Ker.HatLat.hatA_tens D S T C _ _ (fullStd S.rank) (fullSmul Lv.ne_bot ⟨C.X.Λ_fg, C.X.Λ_span⟩)
  have hfull0 := GlobalTheory.Ker.HatLat.hatA_tens D S T C _ _ (fullStd S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have hKer : ∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ),
      tr S T e k₀ y ∈ liftL S T βS βT Pg Q e →
      y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ) := by
    intro y hy hL
    obtain ⟨-, hL2, hL3⟩ := hL
    have h1 : partAt (cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) :=
      (hgen _ (hz y)).2.1 ⟨by rw [← hF]; exact hL2, fun PP hPP => by rw [← hF]; exact hL3 PP hPP⟩
    have h2 : partAt (1 - cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) :=
      partAt_mem_hatA S T _ _ _ (GlobalTheory.T.complementary_idempotent_in_integral_closure D Pg Q e he) (hfinW _ y (tmono hA1 hy))
    have h3 := add_mem h1 h2
    rw [partAt_add_one_sub, ← h𝔪] at h3
    exact tens_inter hcop hy ((hfull.2.1 y).1 h3)
  have hSurj : ∀ x : WO S T, IsHalf (cA D e) x → IsIntM (frMapAdj S T βS βT x) →
      ∃ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ),
        x + tr S T e k₀ y ∈ liftL S T βS βT Pg Q e := by
    intro x hx hxI
    obtain ⟨z₀, hz₀⟩ : ∃ z, z = actO S T k₀⁻¹ 1 (-x) := ⟨_, rfl⟩
    have hneg : IsHalf (cA D e) (-x) := fun i j => by rw [Matrix.neg_apply, mul_neg, hx i j]
    have hinv : actO S T k₀ 1 z₀ = -x := by
      have e1 : mt T (1 : GA D T) = 1 := rfl
      have e2 : mt S k₀ * mt S k₀⁻¹ = 1 := by
        rw [show mt S k₀ * mt S k₀⁻¹ = mt S (k₀ * k₀⁻¹) from rfl, mul_inv_cancel]; rfl
      rw [hz₀]
      simp only [actO, inv_inv, e1, Matrix.one_mul]
      rw [Matrix.mul_assoc, e2, Matrix.mul_one]
    have hz0h : IsHalf (cA D e) z₀ := by
      have e3 : z₀ = partAt (cA D e) z₀ := by
        rw [hz₀]
        conv_lhs => rw [← partAt_of_isHalf hneg]
        rw [actO_partAt]
      rw [e3]; exact isHalf_partAt hc _
    have hadj : adjA S T βS βT a z₀ = -frMapAdj S T βS βT x := by
      rw [← hmov.2.2 z₀ hz0h, hinv, frMapAdj_neg]
    have hz0mem : z₀ ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) :=
      ((hgen z₀ hz0h).1).1 (by rw [hadj]; exact fun i j => by rw [Matrix.neg_apply]; exact neg_mem (hxI i j))
    have hN : 0 < Ideal.absNorm Lv.𝔪 :=
      Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact Lv.ne_bot)
    obtain ⟨y₁, hy₁, u', hu', hzu⟩ := (hfull0.2.2.1 z₀ hz0mem).2 _ hN
    have hNu := nsmul_mem_hatA S T (Ideal.absNorm_mem Lv.𝔪) C.X.Λ hu'
    obtain ⟨g, hg, m, hm, hgm⟩ : ∃ g ∈ Ideal.span {2} * conjI Lv.𝔪, ∃ m ∈ Lv.𝔪, g + m = 1 := by
      have h0 := hcop
      rw [Ideal.isCoprime_iff_sup_eq] at h0
      exact Submodule.mem_sup.1 (h0 ▸ Submodule.mem_top)
    have hgE : (g : D.host.E) = 1 - (m : D.host.E) := by
      have h := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hgm
      rw [map_add, map_one] at h
      exact eq_sub_of_add_eq h
    refine ⟨(g : D.host.E) • y₁, ?_, ?_⟩
    · rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy₁ ⊢
      intro k; exact Submodule.smul_mem_smul hg (hy₁ k)
    · have hmy : (m : D.host.E) • y₁ ∈ tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ) := by
        rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy₁ ⊢
        intro k; exact Submodule.smul_mem_smul hm (hy₁ k)
      have hyg : (g : D.host.E) • y₁ - y₁ = -((m : D.host.E) • y₁) := by
        rw [hgE]; ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
        rw [sub_mul, one_mul, sub_sub_cancel_left]
      have hdiff : partAt (cA D e) (finW S T ((g : D.host.E) • y₁)) - z₀ ∈
          hatA S T (tens (stdL D.host.E S.rank) (Lv.𝔪 • C.X.Λ)) := by
        have e4 : partAt (cA D e) (finW S T ((g : D.host.E) • y₁)) - z₀ =
            partAt (cA D e) (-finW S T ((m : D.host.E) • y₁) - Ideal.absNorm Lv.𝔪 • u') := by
          conv_lhs => rw [← partAt_of_isHalf hz0h]
          rw [← partAt_sub, hzu, ← finW_neg, ← hyg, finW_sub]
          congr 1; abel
        rw [e4]
        exact hP _ _ (sub_mem (neg_mem (hfinW _ _ hmy)) hNu)
      have hdh : IsHalf (cA D e) (partAt (cA D e) (finW S T ((g : D.host.E) • y₁)) - z₀) :=
        fun i j => by rw [Matrix.sub_apply, mul_sub, hz _ i j, hz0h i j]
      obtain ⟨h1, h3⟩ := (hgen _ hdh).2.2 (by rw [← h𝔪]; exact hdiff)
      have hsum : x + tr S T e k₀ ((g : D.host.E) • y₁) =
          actO S T k₀ 1 (partAt (cA D e) (finW S T ((g : D.host.E) • y₁)) - z₀) := by
        rw [actO_sub, hinv, tr_eq]; abel
      have hF' := hmov.2.2 _ hdh
      refine ⟨fun i j => ?_, ?_, fun PP hPP => ?_⟩
      · have h5 : IsHalf (cA D e) (tr S T e k₀ ((g : D.host.E) • y₁)) := isHalf_partAt hc _
        rw [Matrix.add_apply, mul_add, hx i j, h5 i j]
      · rw [hsum, hF']; exact h1
      · rw [hsum, hF']; exact h3 PP hPP
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x)
  · obtain ⟨y, hy, hyL⟩ := hSurj x hx.1 hx.2
    have key : ∀ c : LvCls C Lv, c = QuotientAddGroup.mk ⟨y, hy⟩ ↔
        (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E) - y ∈
          tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ) := by
      intro c
      conv_lhs => rw [← QuotientAddGroup.out_eq' c]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg,
        neg_add_eq_sub, ← neg_mem_iff, neg_sub]
    have hiff : ∀ c : LvCls C Lv, x + tr S T e k₀ (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E) ∈
        liftL S T βS βT Pg Q e ↔ c = QuotientAddGroup.mk ⟨y, hy⟩ := by
      intro c
      rw [key]
      constructor
      · intro hcL
        refine hKer _ (sub_mem c.out.2 hy) ?_
        rw [tr_sub]
        have := sub_mem hcL hyL
        rwa [add_sub_add_left_eq_sub] at this
      · intro hm
        have := add_mem hyL (hIn2 _ hm)
        rwa [tr_sub, add_add_sub_cancel] at this
    rw [finsum_eq_single _ (QuotientAddGroup.mk ⟨y, hy⟩ : LvCls C Lv) (fun c hc' => by
      rw [indL, if_neg (fun h => hc' ((hiff c).1 h)), mul_zero])]
    set c₀ : LvCls C Lv := QuotientAddGroup.mk ⟨y, hy⟩ with hc₀
    have hw : x + tr S T e k₀ (c₀.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E) ∈ liftL S T βS βT Pg Q e :=
      (hiff c₀).2 rfl
    change _ = _ * indL (liftL S T βS βT Pg Q e) (x + tr S T e k₀ (c₀.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))
    rw [indL, if_pos hw, mul_one, hdat _ (neg_mem c₀.out.2), thPDatum, if_pos hx]
    have hwI := hInt _ c₀.out.2
    have hnI : IsIntM (frMapAdj S T βS βT (-tr S T e k₀ (c₀.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) := by
      rw [frMapAdj_neg]; exact fun i j => by rw [Matrix.neg_apply]; exact neg_mem (hwI i j)
    have hred : ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT
        (tr S T e k₀ (-(c₀.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) = redM PP (frMapAdj S T βS βT x) := by
      intro PP hPP
      have h1 := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x _ hx.2 hwI).2 PP
      rw [hw.2.2 PP hPP] at h1
      have h3 := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT _ _ hwI hnI).2 PP
      rw [add_neg_cancel, redM_frMapAdj_zero] at h3
      rw [tr_neg, eq_neg_of_add_eq_zero_right h3.symm, eq_neg_of_add_eq_zero_left h1.symm]
    refine congrArg₂ (· * ·) (omegaK_congr Pg (fun PP hPP => (hred PP (Finset.mem_union_left _ hPP)).symm))
      (omegaQ_congr Q T.rank ξ (-1) (fun PP hPP => (hred PP (Finset.mem_union_right _ hPP)).symm))
  · rw [thPDatum, if_neg hx]
    refine (finsum_eq_zero_of_forall_eq_zero fun c => ?_).symm
    rw [indL, if_neg, mul_zero]
    intro h
    have hwI := hInt _ (c.out : _).2
    have hnI : IsIntM (frMapAdj S T βS βT (-tr S T e k₀ (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E))) := by
      rw [frMapAdj_neg]; exact fun i j => by rw [Matrix.neg_apply]; exact neg_mem (hwI i j)
    have h5 : IsHalf (cA D e) (tr S T e k₀ (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) := isHalf_partAt hc _
    refine hx ⟨fun i j => ?_, ?_⟩
    · have := h.1 i j
      rw [Matrix.add_apply, mul_add, h5 i j] at this
      exact add_right_cancel this
    · have := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT _ _ h.2.1 hnI).1
      rwa [add_neg_cancel_right] at this

end GlobalTheory.LiftLevel.DatSum
