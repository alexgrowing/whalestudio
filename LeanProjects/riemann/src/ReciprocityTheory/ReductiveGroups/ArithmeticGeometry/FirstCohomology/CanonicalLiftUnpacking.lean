import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Zero

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_zero_qk (hB : D.TauBimult) (k : ℕ) :
    ∃ p0 : QkPt D F k, p0.y = 0 ∧ p0.g.IsZero ∧ p0.g.IsAdd p0.g p0.g := by
  obtain ⟨g, hg⟩ := exists_zero_gt (D := D) (F := F)
  have hz := (isZero_iff g).1 hg
  have hadd : g.IsAdd g g := by
    rw [isAdd_iff]
    refine ⟨by rw [hz.1, _root_.mul_one], fun χ y J hJ => ?_⟩
    have hc := isCub_cubV (c := D.cub) hJ
    rw [hz.2 χ y J hJ, hz.1, _root_.one_mul, _root_.one_mul]
    exact (hc.s01 _ _ _).trans (hc.face _ _)
  have hiota : GtPtF.IsIota (0 : D.X) g := by
    rw [isIota_iff]
    refine ⟨by rw [hz.1, cPoint_zero], fun χ y J hJ => ?_⟩
    have hc := isCub_cubV (c := D.cub) hJ
    have h1 := tau_mul (σ := 𝟙 (TF (R := R) F)) (z := y) (J := J) hJ hB 0 0 χ
    simp only [th, add_zero, cPoint_zero, hc.face, _root_.mul_one, Over.id_left] at h1
    rw [add_zero] at h1
    rw [hz.2 χ y J hJ]
    exact (mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)).symm
  exact ⟨⟨0, g, ⟨g, ⟨fun _ => g, hg, fun _ => hadd, rfl⟩, hiota⟩⟩, rfl, hg, hadd⟩

end Zero

theorem alpha_unpack {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t)
    (hT : P.TorsionIso) (hQ : QkActExistsStatement) (α : 𝓞 E) (N : ℕ) (hN : 1 ≤ N)
    (hαN : letI := H.starRing; α * star α = (N : 𝓞 E)) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing V) F] (p : QkPt P.D.toPre F (1 * N)) (x : TFK (R := V) F ⟶ P.A.A)
    (hx : P.ToA F (1 * N) p x) (hxα : x ≫ P.oA.act α = 1) :
    letI := H.starRing
    ∃ (z : P.D.toPre.X) (q : QkPt P.D.toPre F (1 * N)) (h g0 : GtPtF P.D.toPre F),
      p.y = -(star α • z) ∧ GtAct P.oD α p.g q.g ∧ GtPtF.IsIota z h ∧ q.g.IsAdd h g0 ∧ g0.IsZero := by
  letI := H.starRing
  have hαN' : α * star α = (N : 𝓞 E) := hαN
  have hB : P.D.toPre.TauBimult := P.D.tau_bimult
  obtain ⟨p0, hy0, hz0, hadd0⟩ := exists_zero_qk (F := F) hB (1 * N)
  obtain ⟨f, hf1, -, hf3, hf4, hf5, -⟩ := hT F (1 * N) (by omega)
  obtain ⟨p', hp'⟩ := hQ E H V t P F (1 * N) α p
  have hfp' := hf5 α p p' hp'
  obtain ⟨q, hqy, hGt, hqe⟩ := hp'
  have hf0 : f p0 = 1 := by
    have h := hf4 p0 p0 p0 ⟨p0, by rw [hy0, add_zero], hadd0, qk_equiv_refl hB p0⟩
    exact (mul_left_cancel ((_root_.mul_one _).trans h)).symm
  have hfq : f q = f p0 := by
    rw [(hf3 q p').2 hqe, hfp', ← (hf1 p x).1 hx, hxα, hf0]
  obtain ⟨z, hz, h, hIota, hAdd⟩ := (hf3 q p0).1 hfq
  refine ⟨z, q, h, p0.g, ?_, hGt, hIota, hAdd, hz0⟩
  have e : α • p.y + (1 * N) • z = 0 := by rw [← hqy, ← hz, hy0]
  have e' := congrArg (fun w => star α • w) e
  simp only [smul_add, smul_zero, smul_smul] at e'
  have key : ∀ w : P.D.toPre.X, (1 * N) • w = N • w := fun w => by rw [Nat.one_mul]
  rw [smul_comm (star α) (1 * N) z, _root_.mul_comm (star α) α, hαN', Nat.cast_smul_eq_nsmul,
    ← key p.y, ← smul_add] at e'
  haveI : Module.Free ℤ P.D.toPre.X := P.D.toPre.freeX
  rw [← Nat.cast_smul_eq_nsmul ℤ] at e'
  have e3 : p.y + star α • z = 0 := (smul_eq_zero.1 e').resolve_left (by omega)
  exact eq_neg_of_add_eq_zero_left e3

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftUnpacking
