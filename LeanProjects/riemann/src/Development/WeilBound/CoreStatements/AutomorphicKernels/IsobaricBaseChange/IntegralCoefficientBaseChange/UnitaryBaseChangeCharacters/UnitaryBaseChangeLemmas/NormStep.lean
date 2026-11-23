import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ExistsPolyOfCommute

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem norm_step [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) {n : ℕ}
    (γ J Ji Hn Hi : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X])
    (hγ : ∀ i j, γ i j ∈ intL L) (hJ : ∀ i j, J i j ∈ intL L) (hJi : ∀ i j, Ji i j ∈ intL L)
    (hH : ∀ i j, Hn i j ∈ intL L) (hHi : ∀ i j, Hi i j ∈ intL L)
    (hJJ : J * Ji = 1) (hHH : Hn * Hi = 1) (hJh : cT σ J = J) (hHh : cT σ Hn = Hn)
    (hγJ : cT σ γ * J * γ = J) (hγH : cT σ γ * Hn * γ = Hn)
    (hch : γ.charpoly = Q₀.map (intL L).subtype) (hsep : Q₀.Separable) :
    ∃ b : GL (Fin n) L, b.val * γ = γ * b.val ∧ cT σ b.val * J * b.val = Hn := by
  set sO := GlobalTheory.NormEq.sigO σ h.2.1 with hsO
  let Φ : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L := (intL L).subtype.mapMatrix
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext i j; exact congrFun (congrFun hab i) j
  have hΦcT : ∀ M, Φ (cT sO M) = cT σ (Φ M) := fun M => rfl
  let γO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨γ i j, hγ i j⟩
  let JO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨J i j, hJ i j⟩
  let JiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Ji i j, hJi i j⟩
  let HO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Hn i j, hH i j⟩
  let HiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Hi i j, hHi i j⟩
  have eγ : Φ γO = γ := rfl
  have eJ : Φ JO = J := rfl
  have eJi : Φ JiO = Ji := rfl
  have eH : Φ HO = Hn := rfl
  have eHi : Φ HiO = Hi := rfl
  have hJJO : JO * JiO = 1 := hΦinj (by rw [map_mul, map_one, eJ, eJi, hJJ])
  have hJJO' : JiO * JO = 1 := mul_eq_one_comm.1 hJJO
  have hHHO : HO * HiO = 1 := hΦinj (by rw [map_mul, map_one, eH, eHi, hHH])
  have hHHO' : HiO * HO = 1 := mul_eq_one_comm.1 hHHO
  have hγJO : cT sO γO * JO * γO = JO := hΦinj (by rw [map_mul, map_mul, hΦcT, eγ, eJ, hγJ])
  have hγHO : cT sO γO * HO * γO = HO := hΦinj (by rw [map_mul, map_mul, hΦcT, eγ, eH, hγH])
  have hJhO : cT sO JO = JO := hΦinj (by rw [hΦcT, eJ, hJh])
  have hHhO : cT sO HO = HO := hΦinj (by rw [hΦcT, eH, hHh])
  have hchO : γO.charpoly = Q₀ := by
    apply Polynomial.map_injective _ (intL L).subtype_injective
    rw [← hch, ← eγ]
    exact (Matrix.charpoly_map γO (intL L).subtype).symm
  have hsepO : γO.charpoly.Separable := hchO ▸ hsep
  have hcsr : GlobalTheory.UTr.IsCsr sO Q₀ := hchO ▸ isCsr_charpoly sO γO JO JiO hJJO' hγJO
  let P : GlobalTheory.UTr.Csr sO := ⟨Q₀, hcsr⟩
  have hg : aeval γO P.1 = 0 := by
    show aeval γO Q₀ = 0
    rw [← hchO]; exact Matrix.aeval_self_charpoly γO
  let ev := GlobalTheory.UTr.evalMat P γO hg
  have hev : ∀ r : (intL L)[X], ev (aeval (GlobalTheory.UTr.root P) r) = aeval γO r := fun r => by
    rw [← aeval_algHom_apply, GlobalTheory.UTr.evalMat_root]
  have hevinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun z hz => ?_
    obtain ⟨r, rfl⟩ := GlobalTheory.UTr.exists_aeval_root P z
    rw [hev] at hz
    have hd := GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt (intL L) n γO r hsepO hz
    rw [hchO] at hd
    exact (GlobalTheory.UTr.aeval_root_eq_zero_iff P).2 hd

  let γiO := JiO * cT sO γO * JO
  have hγi : γiO * γO = 1 := by
    show JiO * cT sO γO * JO * γO = 1
    rw [Matrix.mul_assoc JiO, Matrix.mul_assoc JiO, hγJO, hJJO']
  let gU : UJ sO JO := ⟨⟨γO, γiO, mul_eq_one_comm.1 hγi, hγi⟩, hγJO⟩
  have hcT : ∀ z, cT sO (ev z) * JO = JO * ev (GlobalTheory.UTr.conj P z) := fun z => GlobalTheory.UTr.cT_evalMat P gU hg z

  have hxc : (JiO * HO) * γO = γO * (JiO * HO) := by
    have hA : cT sO γO * (JO * γO * JiO) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγJO, hJJO]
    have hA' : (JO * γO * JiO) * cT sO γO = 1 := mul_eq_one_comm.1 hA
    calc JiO * HO * γO = JiO * ((JO * γO * JiO) * cT sO γO) * HO * γO := by rw [hA', Matrix.mul_one]
      _ = γO * JiO * (cT sO γO * HO * γO) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc JiO JO, hJJO', Matrix.one_mul]
      _ = γO * (JiO * HO) := by rw [hγHO, Matrix.mul_assoc]
  obtain ⟨p, hp⟩ := exists_poly_of_commute γO (JiO * HO) hsepO hxc
  let tz : GlobalTheory.UTr.Alg P := aeval (GlobalTheory.UTr.root P) p
  have htO : ev tz = JiO * HO := by rw [hev, ← hp]

  let tiO := HiO * JO
  have htiO : (JiO * HO) * tiO = 1 := by
    show JiO * HO * (HiO * JO) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc HO, hHHO, Matrix.one_mul, hJJO']
  have hdet : IsUnit (ev tz).det := by
    rw [htO]
    exact isUnit_iff_exists_inv.2 ⟨tiO.det, by rw [← Matrix.det_mul, htiO, Matrix.det_one]⟩
  have hunit : IsUnit tz := by
    have h0 : aeval tz (ev tz).charpoly = 0 := hevinj (by
      rw [← aeval_algHom_apply, map_zero]; exact Matrix.aeval_self_charpoly (ev tz))
    have hc0 : IsUnit ((ev tz).charpoly.coeff 0) := by
      have := Matrix.det_eq_sign_charpoly_coeff (ev tz)
      rw [this] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    have e := congrArg (aeval tz) (X_mul_divX_add (ev tz).charpoly)
    rw [h0, map_add, map_mul, aeval_X, aeval_C] at e
    have hu : IsUnit (tz * aeval tz (ev tz).charpoly.divX) := by
      rw [eq_neg_of_add_eq_zero_left e]
      exact (hc0.map _).neg
    exact isUnit_of_mul_isUnit_left hu
  let T : (GlobalTheory.UTr.Alg P)ˣ := hunit.unit

  have hcTJi : cT sO JiO = JiO := by
    have h1 : cT sO JiO * JO = 1 := by
      rw [← hJhO, ← cT_mul, hJJO, cT_one]
    calc cT sO JiO = cT sO JiO * (JO * JiO) := by rw [hJJO, Matrix.mul_one]
      _ = JiO := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hconj : GlobalTheory.UTr.conj P tz = tz := by
    apply hevinj
    have h1 : JO * ev (GlobalTheory.UTr.conj P tz) = JO * ev tz := by
      rw [← hcT, htO, cT_mul, hHhO, hcTJi, Matrix.mul_assoc, hJJO', Matrix.mul_one, ← Matrix.mul_assoc, hJJO,
        Matrix.one_mul]
    have h2 := congrArg (JiO * ·) h1
    simpa only [← Matrix.mul_assoc, hJJO', Matrix.one_mul] using h2
  have hT : T ∈ GlobalTheory.UTr.plus P := GlobalTheory.UTr.mem_plus.2 (by rw [IsUnit.unit_spec]; exact hconj)
  have hsepP : (P : (intL L)[X]).Separable := hsep
  obtain ⟨u, hu⟩ := GlobalTheory.NormEq.normU_surj L σ ϖ q h P hsepP T hT
  have hu' : (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u = tz := by
    have := congrArg (fun z : (GlobalTheory.UTr.Alg P)ˣ => (z : GlobalTheory.UTr.Alg P)) hu
    simpa [GlobalTheory.UTr.normU, T] using this
  let Ψ : GlobalTheory.UTr.Alg P →* Matrix (Fin n) (Fin n) L := (Φ.comp ev.toRingHom : GlobalTheory.UTr.Alg P →+* _)
  refine ⟨Units.map Ψ u, ?_, ?_⟩
  · show Φ (ev u) * γ = γ * Φ (ev u)
    rw [← eγ, ← map_mul, ← map_mul]
    congr 1
    rw [← GlobalTheory.UTr.evalMat_root P γO hg, ← map_mul, ← map_mul, mul_comm]
  · show cT σ (Φ (ev u)) * J * Φ (ev u) = Hn
    rw [← hΦcT, ← eJ, ← map_mul, ← map_mul, hcT, Matrix.mul_assoc, ← map_mul, mul_comm (GlobalTheory.UTr.conj P _), hu',
      htO, ← Matrix.mul_assoc, hJJO, Matrix.one_mul, eH]

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
