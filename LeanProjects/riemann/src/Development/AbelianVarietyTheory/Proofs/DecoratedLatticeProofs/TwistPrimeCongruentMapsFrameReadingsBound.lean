import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport

noncomputable section

namespace GlobalTheory.Transport.TwistRead

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open GlobalTheory.Transport.LevelDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
  {a b : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

omit [NumberField E] [StarRing E] in
theorem toMatrix_inFr (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    LinearMap.toMatrix' f'.toLinearMap * LinearMap.toMatrix' (inFr f f' x) = LinearMap.toMatrix' x * LinearMap.toMatrix' f.toLinearMap := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  exact congrArg _ (LinearMap.ext fun z => f'.apply_symm_apply _)

theorem map_ptFr {n : ℕ} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)}
    (hPQ : P ∈ Q) (hPG : P ∉ SG) :
    (LinearMap.toMatrix' (ptFr p P).toLinearMap).map (algebraMap E (P.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, ptFr_of_mem p hPG hPQ]
  exact (h.fr ⟨P, hPQ⟩ i j).symm

omit [StarRing E] in
theorem map_inv_mul_map {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) :
    ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) *
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_read {g : GL (Fin a) (AfE F E)} {g' : GL (Fin b) (AfE F E)} {p : DecoF E a ST SG Q} {p' : DecoF E b ST SG Q}
    (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG) (x : HomE E a b) :
    (LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x)).map (algebraMap E (P.adicCompletion E)) =
      (mid g g' x).map (adAt F P) := by
  have f1 := congrArg (fun A => Matrix.map A (algebraMap E (P.adicCompletion E))) (toMatrix_inFr (ptFr p P) (ptFr p' P) x)
  simp only [Matrix.map_mul] at f1
  rw [map_ptFr h hPQ hPG, map_ptFr h' hPQ hPG] at f1
  have hx : (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E)) = (adMat F x).map (adAt F P) :=
    Matrix.ext fun i j => (adAt_inclE F P _).symm
  unfold mid
  rw [Matrix.map_mul, Matrix.map_mul, ← hx, Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, map_inv_mul_map, Matrix.one_mul]

theorem read_sub_le {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)} {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST SG Q}
    (hp : IsPtOf hc k p) (hpN : p.deco.1.N = stdLat E a) (hp' : IsPtOf hc k' p') (hpN' : p'.deco.1.N = stdLat E b)
    (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG)
    (M₀ : ℕ) (x x₀ : HomE E a b)
    (h : ∀ r s, Valued.v (adAt F P ((mid y y' x - adMat F x₀) r s)) ≤ Valued.v ((M₀ : ℕ) : P.adicCompletion E)) (r : Fin b) (s : Fin a) :
    P.valuation E ((LinearMap.toMatrix' (inFr (ptFr q P) (ptFr q' P) x) - LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x₀)) r s) ≤
      P.valuation E ((M₀ : ℕ) : E) := by
  have hd : mid (y * k) (y' * k') x - mid k k' x₀ =
      ((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * (mid y y' x - adMat F x₀) *
        (k : Matrix (Fin a) (Fin a) (AfE F E)) := by
    unfold mid
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hA : ∀ r s, Valued.v (adAt F P (((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (hpN' ▸ hp'.lat) (carries_one (F := F) b) le_rfl r s
    rwa [mul_one] at this
  have hK : ∀ r s, Valued.v (adAt F P ((k : Matrix (Fin a) (Fin a) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (carries_one (F := F) a) (hpN ▸ hp.lat) le_rfl r s
    rwa [inv_one, one_mul] at this
  have e1 := congrFun (congrFun (map_read hq hq' hPQ hPG x) r) s
  have e2 := congrFun (congrFun (map_read hp hp' hPQ hPG x₀) r) s
  simp only [Matrix.map_apply] at e1 e2
  rw [← valued_algebraMap, ← valued_algebraMap, map_natCast, Matrix.sub_apply, map_sub, e1, e2, ← map_sub, ← Matrix.sub_apply, hd]
  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, map_mul]
  refine (mul_le_of_le_one_right' (hK j s)).trans ?_
  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_left' (hA r l)).trans (h l j)

end Gen

end GlobalTheory.Transport.TwistRead

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.TwistRead

theorem qread : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  intro B X I u a i P hP hd p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hC r s
  rw [frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr]
  exact read_sub_le hp hpN hp' hpN' hq hq' hP (Finset.disjoint_right.1 hd hP) M₀ x x₀ (fun r s => hC r s) r s

end GlobalTheory.Transport.TwistRead
