import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TilX Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopPtModel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_mul {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (a b : GL (Fin N) (AfE F E)) :
    ((a * b : GL (Fin N) (AfE F E)).1).map (adAt F P) = a.1.map (adAt F P) * b.1.map (adAt F P) := by
  rw [Units.val_mul, Matrix.map_mul]

theorem adAt_inv_one {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) {a : GL (Fin N) (AfE F E)} (h : a.1.map (adAt F P) = 1) :
    ((a⁻¹ : GL (Fin N) (AfE F E)).1).map (adAt F P) = 1 := by
  have := adAt_mul P a a⁻¹
  rw [mul_inv_cancel, h, one_mul, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this.symm

theorem adAt_of_prV {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) {k : GL (Fin N) (AfE F E)}
    (h1 : bc (prV (E := E) (P.under (𝓞 F))) k = 1) : k.1.map (adAt F P) = 1 := by
  refine Matrix.ext fun i j => ?_
  have h2 : prV (E := E) (P.under (𝓞 F)) (k.1 i j - (1 : Matrix (Fin N) (Fin N) (AfE F E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin N) _ => g.1 i j) h1
    simp only [Units.val_one] at h3
    have h4 : prV (E := E) (P.under (𝓞 F)) (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem prV_of_adAt {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) {k : GL (Fin N) (AfE F E)}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → k.1.map (adAt F w) = 1) : bc (prV (E := E) v) k = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show prV (E := E) v (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j
  have h2 : prV (E := E) v (k.1 i j - (1 : Matrix (Fin N) (Fin N) (AfE F E)) i j) = 0 := by
    refine (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).1.2 fun w hw => ?_
    have h3 : adAt F w (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j := congrFun (congrFun (h w hw) i) j
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h2
  refine h2.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

theorem topPt_base {u : B.Word} {a : I.ι} {k : GA B (B.R.N B.R.m)} [NeZero (B.R.N B.R.m - 1)] (h : I.TopPt l Z u a k) :
    PtOf k (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (DecoF.base _ _ _ _ _)) := by
  have := h (DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _) ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rwa [one_mul] at this

theorem topPt_last (hI : I.Ok) {u : B.Word} {a : I.ι} {k : GA B (B.R.N B.R.m)} [NeZero (B.R.N B.R.m - 1)] (h : I.TopPt l Z u a k)
    (P : I.Q a) (i : Fin (B.R.N B.R.m)) : adAt B.host.F P.1 (k.1 i (Br.iL (N_m_succ B.R))) =
      algebraMap B.host.E _ ((Pi.single (Br.iL (N_m_succ B.R)) ((X.piT u : 𝓞 B.host.E) : B.host.E) : Fin _ → B.host.E) i) := by
  have hPr := (base_fields_primes_ok B X).2.1
  have h1 := (topPt_base I l Z h).fr P i (Br.iL (N_m_succ B.R))
  have h2 := tilFr_fr_last (N_m_succ B.R) (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
    (fun P : I.Q a => ((TwistPrimes.twist_primes_away I hI).2 u a P.1 P.2).2.1) (DecoF.base _ _ _ _ _) P
  exact h1.trans (congrArg (fun x => algebraMap B.host.E _ (x i)) h2)

theorem exists_topPt (hI : I.Ok) (hP : TC.Pins B X) (u : B.Word) (a : I.ι) : ∃ k : GA B (B.R.N B.R.m),
    (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) k = 1) ∧
    (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = B.R.N B.R.m →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) ∧
    I.TopPt l Z u a k := by
  have hX := (base_fields_primes_ok B X).1
  have hPr := (base_fields_primes_ok B X).2.1
  haveI : NeZero (B.R.N B.R.m) := ⟨by have := N_m_succ B.R; omega⟩
  have hq := (TwistPrimes.twist_primes_away I hI).2 u a
  obtain ⟨k, h1, h2, h3⟩ := BasePoint.exists_kStd X hPr u (B.R.N B.R.m)
  obtain ⟨t, t1, t2, t3⟩ := TwUnit.exists_tw B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a)
    (fun P hP => (hq P hP).1) (X.piT u) (fun P hP => (hq P hP).2.1)
  have t4 : ∀ w, w ∉ I.Q a → conjPrime₂ w ∉ I.Q a → t.1.map (adAt B.host.F w) = 1 := fun w a1 a2 => by
    refine Matrix.ext fun i j => ?_
    exact (t3 w a1 a2 i j).trans Matrix.one_apply.symm
  have hcc : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext x
    rw [mem_conjP, mem_conjP, cO_cO]
  have hun : ∀ Q : HeightOneSpectrum (𝓞 B.fields.E), (conjPrime₂ Q).under (𝓞 B.fields.F) = Q.under (𝓞 B.fields.F) := fun Q => by
    ext r
    have e : cO B.fields.E (algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r) = algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r :=
      RingOfIntegers.ext (hX.star_F (r : B.fields.F))
    show algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r ∈ (conjPrime₂ Q).asIdeal ↔ algebraMap (𝓞 B.fields.F) (𝓞 B.fields.E) r ∈ Q.asIdeal
    rw [mem_conjP, e]
  refine ⟨k * t, TopCh.KStd.exists_ptOf_mul_K1 _ _ _ k t t1 h1, fun v hv hu => ?_, fun P r j hr => ?_,
    TilQ.pt_tilF_gen I hI hP l Z u a k t h1 h2 h3 t1 t2⟩
  · rw [map_mul, h2 v hv, one_mul]
    exact prV_of_adAt v fun w hw => t4 w (fun h => hu ⟨w, h, hw⟩) (fun h => hu ⟨_, h, (hun w).trans hw⟩)
  · have e1 := adAt_inv_one P.1 (t4 P.1 (fun h => (hq _ h).1.1 P.2) (fun h => (hq _ h).1.2.2.1 ((hcc P.1).symm ▸ P.2)))
    have e2 := adAt_mul (F := B.host.F) (E := B.host.E) P.1 t⁻¹ k⁻¹
    rw [e1, one_mul, ← _root_.mul_inv_rev] at e2
    have e3 : adAt B.host.F P.1 (((k * t)⁻¹ : GA B (B.R.N B.R.m)).1 r j) = adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j) :=
      congrFun (congrFun e2 r) j
    exact e3 ▸ h3 P r j hr

theorem not_topPt_one (hI : I.Ok) {u : B.Word} {a : I.ι} [NeZero (B.R.N B.R.m - 1)] (P : I.Q a)
    (hpi : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 1) : ¬ I.TopPt l Z u a 1 := fun h => by
  have h1 := topPt_last I l Z hI h P (Br.iL (N_m_succ B.R))
  rw [Pi.single_eq_same, Units.val_one, Matrix.one_apply_eq, map_one] at h1
  exact hpi ((algebraMap B.host.E _).injective (h1.symm.trans (map_one _).symm))

end GlobalTheory.Mem.Col2.TopPtModel

end
