import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.XUniRead

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem red_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {q : ℕ} (hq : q.Prime)
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (y : v.adicCompletionIntegers (maximalRealSubfield L))
    (hy : Valued.v (y : v.adicCompletion (maximalRealSubfield L)) < 1) : red y = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharZero (v.adicCompletion (maximalRealSubfield L)) :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield L) _).injective
  have hp : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hne : RingHom.ker red ≠ ⊥ := by
    intro h
    have h1 : ((q : ℕ) : v.adicCompletionIntegers (maximalRealSubfield L)) ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      (z : v.adicCompletion (maximalRealSubfield L))) h1
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h2
    exact hq.ne_zero h2
  have hm : RingHom.ker red = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  rw [← RingHom.mem_ker, hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨z, hz⟩ := hu.exists_right_inv
  have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      Valued.v (z : v.adicCompletion (maximalRealSubfield L))) hz
  simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
  have hz1 : Valued.v (z : v.adicCompletion (maximalRealSubfield L)) ≤ 1 := z.2
  have h3 := mul_le_mul_right hz1 (Valued.v (y : v.adicCompletion (maximalRealSubfield L)))
  rw [h2, mul_one] at h3
  exact absurd hy (not_lt.2 h3)

private theorem intLift_coe (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : v.adicCompletionIntegers (maximalRealSubfield L)) :
    NX.intLift v (y : v.adicCompletion (maximalRealSubfield L)) = y := by
  unfold NX.intLift
  rw [dif_pos y.2]

private theorem sum_top {R : Type} [CommRing R] {n r : ℕ} (h : r ≤ n) (X : Matrix (Fin n) (Fin n) R) :
    (∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then X a b else 0) = NX.supSum r (NX.topR h X) := by
  unfold NX.supSum NX.topR
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun a _ ha => Finset.sum_eq_zero fun b _ => if_neg fun hh => ha ⟨⟨a.val, by omega⟩, by simp, Fin.ext rfl⟩) fun a _ => ?_
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun b _ hb => if_neg fun hh => hb ⟨⟨b.val, hh.2⟩, by simp, Fin.ext rfl⟩) fun b _ => ?_
  refine if_congr ?_ rfl rfl
  simp only [Fin.val_castLE, b.2, and_true]
  exact eq_comm

private theorem supSum_small {R : Type} [CommRing R] {r : ℕ} (h : ¬ 2 ≤ r) (M : Matrix (Fin r) (Fin r) R) :
    NX.supSum r M = 0 := by
  unfold NX.supSum
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (by have := b.2; omega)

private theorem loc_read (s : SplitPlace L) {n r : ℕ} (h : r ≤ n) {q : ℕ} (hq : q.Prime)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (hx : NG.UniRT s r x) :
    NX.IsUniTri r (NX.redMat s.v red (NX.topR h x.val)) ∧ IsUnit (red (NX.intLift s.v (NX.detT r x.val))) ∧
    ((NX.intLift s.v (NX.detT r x.val) : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r x ∧
    ∃ y : s.v.adicCompletionIntegers (maximalRealSubfield L),
      (y : s.v.adicCompletion (maximalRealSubfield L)) = NG.supDiag s r x ∧
      red y = NX.supSum r (NX.redMat s.v red (NX.topR h x.val)) := by
  obtain ⟨⟨⟨X0, hX0⟩, hll⟩, huni⟩ := hx
  obtain ⟨X, hXu, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)),
      IsUnit X.det ∧ ∀ a b, x.val a b = (X a b : s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨X0.val, Matrix.isUnits_det_units X0, fun a b => by rw [← hX0]; rfl⟩
  have hr : ∀ a b, NX.redMat s.v red (NX.topR h x.val) a b = red (X (Fin.castLE h a) (Fin.castLE h b)) := fun a b => by
    simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
    rw [hX, intLift_coe]
  have hd : NX.detT r x.val = ((NX.detT r X : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) := by
    unfold NX.detT
    refine Eq.trans ?_ (RingHom.map_det (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype _).symm
    congr 1
    exact Matrix.ext fun a b => hX _ _
  refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, ?_, ?_, NX.supSum r (NX.topR h X), ?_, ?_⟩
  · rw [hr]
    refine red_zero _ hq red _ ?_
    rw [← hX]
    exact (huni _ _ a.2 b.2).1 hab
  · rw [hr, ← sub_eq_zero, ← map_one red, ← map_sub]
    refine red_zero _ hq red _ ?_
    have := (huni (Fin.castLE h a) (Fin.castLE h a) a.2 a.2).2 rfl
    rw [hX] at this
    exact this
  · rw [hd, intLift_coe]
    have h1 := hXu.map red
    rw [RingHom.map_det, Matrix.twoBlockTriangular_det' (red.mapMatrix X) (fun a : Fin n => r ≤ a.val)
      (fun a ha b hb => red_zero _ hq red _ (by rw [← hX]; exact hll a b ha (not_le.1 hb)))] at h1
    have h2 := isUnit_of_mul_isUnit_left h1
    unfold NX.detT
    rw [RingHom.map_det]
    exact h2
  · rw [hd, intLift_coe, ← hd]
    rfl
  · unfold NG.supDiag
    rw [sum_top h]
    unfold NX.supSum
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hX _ _).symm
    · rfl
  · unfold NX.supSum
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hr _ _).symm
    · exact map_zero _

end Loc

end GlobalTheory.XUniRead

theorem _root_.GlobalTheory.T.complex_typePlaceCharacter_eq_superdiag_addChar_mul_lowerDet : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv0 : Σ kk : Fin 2, D.nd.PlG kk)
    (s : SplitPlace D.host.E) (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv0.1))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ),
    (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
      ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        GlobalTheory.SeriesTie.sideEmb D.ntw i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (τ : (ZMod (D.host.g kv0.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (τ' : (ZMod (D.host.g kv0.1))ˣ →* (↥D.LL0)ˣ),
    (∀ x, ((τ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ' x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (e : NX.Kk D i k →+* ℂ), SideRead i b k e →
    ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ),
    (2 ≤ D.R.r → ∀ y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      ψ₀ (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
        embLL0 D ((θ kv0.1 (Multiplicative.ofAdd (NX.xiRed D kv0 * red y)) : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
    (∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
      (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
        ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ' hy.unit : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (x : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))), NG.UniRT s D.R.r x →
    ∀ uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r x →
      e (NX.gVal D i k b kv0 s red τ (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))) =
        ψ₀ (NG.supDiag s D.R.r x) * ((ξ uu : ℂˣ) : ℂ) := by
  intro D X i k b kv0 s red θ hpsi τ τ' hτ e he ψ₀ hψ₀ ξ hξ x hx uu huu
  classical
  obtain ⟨h1, h2, h3, y, hy, hry⟩ := GlobalTheory.XUniRead.loc_read s (n := D.R.nV) (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
    (D.host.g_prime kv0.1) red x hx
  unfold NX.gVal
  erw [dif_pos h2]
  rw [map_mul, hτ, he, hξ _ h2 uu (huu.trans h3.symm)]
  congr 1
  generalize hM : NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x.val) = M
  erw [hM] at h1 hry
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular h1.1, Finset.prod_eq_one fun a _ => h1.2 a]
    exact isUnit_one
  have hval := NX.glOf_val M hdet
  generalize hu : (Pi.mulSingle kv0 (NX.glOf M) : G0g D.nd) = u
  have hu0 : (u kv0).val = M := by rw [← hu, Pi.mulSingle_eq_same, hval]
  have hu1 : ∀ kv, kv ≠ kv0 → (u kv).val = 1 := fun kv hkv => by rw [← hu, Pi.mulSingle_eq_of_ne hkv]; rfl
  have hm' : u ∈ Formalism.IndefR.NX.U D.nd := fun kv => by
    by_cases hkv : kv = kv0
    · subst hkv; rw [hu0]; exact h1
    · rw [hu1 kv hkv]; exact ⟨Matrix.blockTriangular_one, fun a => Matrix.one_apply_eq a⟩
  have hm : u ∈ D.nexp.U := by rw [X.U_eq]; exact hm'
  unfold NX.psiUTot
  rw [dif_pos hm, hpsi u hm hm', he, psiUOf_apply, Fintype.prod_eq_single kv0 (fun kv hkv => by
    rw [hu1 kv hkv, NX.supSum_one, mul_zero, ofAdd_zero, map_one]), hu0, ← hy]
  by_cases hr : 2 ≤ D.R.r
  · rw [hψ₀ hr y, hry]
  · have h0 : NG.supDiag s D.R.r x = 0 := by
      unfold NG.supDiag
      exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => if_neg (by omega)
    rw [hy, h0, GlobalTheory.XUniRead.supSum_small hr, mul_zero, ofAdd_zero, map_one, Units.val_one, map_one, AddChar.map_zero_eq_one]
