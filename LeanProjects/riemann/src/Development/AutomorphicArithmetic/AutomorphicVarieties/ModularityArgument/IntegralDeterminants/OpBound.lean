import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.AbsBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.RepBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.VecForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEqOfValuedEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.ExistsConjPolynomialDefiniteUnitaryRational
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section Tens

variable {V : Type} [Fintype V] {d : V → ℕ} [DecidableEq (∀ v, Fin (d v))] {H : Type} [Group H]

private noncomputable def tens (M : ∀ v, H →* Matrix (Fin (d v)) (Fin (d v)) ℂ) :
    H →* Matrix (∀ v, Fin (d v)) (∀ v, Fin (d v)) ℂ where
  toFun g := Matrix.of fun i j => ∏ v, M v g⁻¹ (j v) (i v)
  map_one' := by
    ext i j
    simp only [inv_one, map_one, Matrix.of_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨v, hv⟩ := Function.ne_iff.1 h
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg (Ne.symm hv))
  map_mul' g h := by
    ext i j
    have e : ∀ v, M v (g * h)⁻¹ (j v) (i v) = ∑ k, M v h⁻¹ (j v) k * M v g⁻¹ k (i v) := fun v => by
      rw [_root_.mul_inv_rev, map_mul, Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.mul_apply, e]
    rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => mul_comm _ _

private theorem tens_apply (M : ∀ v, H →* Matrix (Fin (d v)) (Fin (d v)) ℂ) (g : H) (i j : ∀ v, Fin (d v)) :
    tens M g i j = ∏ v, M v g⁻¹ (j v) (i v) := rfl

end Tens

section Nu

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private theorem nu_mul (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu]

private theorem nu_one : nu ι 1 = 1 := by
  simp [nu]

private theorem nu_zero : nu ι 0 = 0 := by
  simp [nu]

private theorem nu_nonneg (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _

private theorem nu_prod {α : Type*} (t : Finset α) (f : α → ℂ) : nu ι (∏ a ∈ t, f a) = ∏ a ∈ t, nu ι (f a) :=
  map_prod (⟨⟨nu ι, nu_one ι⟩, nu_mul ι⟩ : ℂ →* ℝ) f t

private theorem nu_pow (x : ℂ) (m : ℕ) : nu ι (x ^ m) = nu ι x ^ m :=
  map_pow (⟨⟨nu ι, nu_one ι⟩, nu_mul ι⟩ : ℂ →* ℝ) x m

variable {E : Type} [Field E] [NumberField E]

private theorem nu_of_val (w : HeightOneSpectrum (𝓞 E)) (ψ : w.adicCompletion E →+* ℂ) (τ : E →+* ℂ)
    (hψ : ∀ x : E, ψ (algebraMap E _ x) = τ x) (hi : ∀ x, nu ι (ψ x) ≤ 1 ↔ Valued.v x ≤ 1)
    (x : w.adicCompletion E) (m : ℕ) (hx : Valued.v x = WithZero.exp (-(m : ℤ))) :
    nu ι (ψ x) = nu ι (τ (unif w : E)) ^ m := by
  set p : w.adicCompletion E := ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) with hp
  have hv : Valued.v p = WithZero.exp (-1 : ℤ) := unif_spec w
  have hτ : ψ p = τ (unif w : E) := hψ _
  have hp0 : p ≠ 0 := Units.ne_zero _
  have hpm : Valued.v (p ^ m) = WithZero.exp (-(m : ℤ)) := by
    rw [map_pow, hv, ← WithZero.exp_nsmul]
    congr 1
    simp
  set y : w.adicCompletion E := x * (p ^ m)⁻¹ with hy
  have hy1 : Valued.v y = 1 := by
    rw [hy, map_mul, map_inv₀, hpm, hx]
    exact mul_inv_cancel₀ (WithZero.exp_ne_zero)
  have hy0 : y ≠ 0 := fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  have h1 : nu ι (ψ y) ≤ 1 := (hi y).2 hy1.le
  have h2 : nu ι (ψ y⁻¹) ≤ 1 := (hi _).2 (by rw [map_inv₀, hy1, inv_one])
  have h3 : nu ι (ψ y) * nu ι (ψ y⁻¹) = 1 := by
    rw [← nu_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, nu_one]
  have h4 : nu ι (ψ y) = 1 := by
    have a0 := nu_nonneg ι (ψ y)
    have b0 := nu_nonneg ι (ψ y⁻¹)
    nlinarith
  have hxy : x = y * p ^ m := by
    rw [hy, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), mul_one]
  rw [hxy, map_mul, nu_mul, h4, one_mul, map_pow, nu_pow, hτ]

end Nu

section Words

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private def IntDet (w : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : GL (Fin n) (w.adicCompletion E)) : Prop :=
  (∀ a b, Valued.v (g.val a b) ≤ 1) ∧ Valued.v g.val.det = WithZero.exp (-(m : ℤ))

private theorem intDet_one (w : HeightOneSpectrum (𝓞 E)) :
    IntDet w 0 (1 : GL (Fin n) (w.adicCompletion E)) := by
  refine ⟨fun a b => ?_, by simp⟩
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

private theorem intDet_mul {w : HeightOneSpectrum (𝓞 E)} {a b : ℕ} {g h : GL (Fin n) (w.adicCompletion E)}
    (hg : IntDet w a g) (hh : IntDet w b h) : IntDet w (a + b) (g * h) := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    exact mul_le_one' (hg.1 i k) (hh.1 k j)
  · rw [Units.val_mul, Matrix.det_mul, map_mul, hg.2, hh.2, ← WithZero.exp_add]
    congr 1
    push_cast
    ring

private theorem intDet_of_KGL {w : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (w.adicCompletion E)}
    (hg : g ∈ GlobalTheory.LFun.KGL w n) : IntDet w 0 g :=
  ⟨((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w g).1 hg).1, by
    simpa using GlobalTheory.HenQ.valued_det_of_KGL hg⟩

end Words

section Places

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem exists_places (w : HeightOneSpectrum (𝓞 E)) (hw : IsSplitAt w) :
    ∃ (φ : InfinitePlace E → (E →+* ℂ)) (u : InfinitePlace E → HeightOneSpectrum (𝓞 E))
      (ψ : ∀ v, (u v).adicCompletion E →+* ℂ),
      (∀ v, InfinitePlace.mk (φ v) = v) ∧ (∀ v x, ψ v (algebraMap E _ x) = φ v x) ∧
      (∀ v x, nu ι (ψ v x) ≤ 1 ↔ Valued.v x ≤ 1) ∧ (∀ v, φ v ∈ Ov ι w ↔ u v = w) ∧
      (∀ τ ∈ Ov ι w, φ (InfinitePlace.mk τ) = τ) ∧
      ∀ v, u v ≠ w → (u v).under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
  let φ : InfinitePlace E → (E →+* ℂ) := fun v =>
    if h : ∃ τ ∈ Ov ι w, InfinitePlace.mk τ = v then h.choose else v.embedding
  have hφ : ∀ v, InfinitePlace.mk (φ v) = v := fun v => by
    by_cases h : ∃ τ ∈ Ov ι w, InfinitePlace.mk τ = v
    · simp only [φ, dif_pos h]
      exact h.choose_spec.2
    · simp only [φ, dif_neg h]
      exact InfinitePlace.mk_embedding v
  have hφw : ∀ v, (∃ τ ∈ Ov ι w, InfinitePlace.mk τ = v) → φ v ∈ Ov ι w := fun v h => by
    simp only [φ, dif_pos h]
    exact h.choose_spec.1
  have hP := fun v => placeHom _ ι E (φ v)
  choose u ψ h1 h2 h3 using hP
  refine ⟨φ, u, ψ, hφ, h1, h2, fun v => (h3 v w).trans eq_comm, ?_, ?_⟩
  · intro τ hτ
    have hv := hφw _ ⟨τ, hτ, rfl⟩
    rcases InfinitePlace.mk_eq_iff.1 (hφ (InfinitePlace.mk τ)) with h | h
    · exact h
    · have h' : ComplexEmbedding.conjugate (φ (InfinitePlace.mk τ)) ∈ Ov ι w := by
        rw [h]
        exact hτ
      exact absurd h' ((placeConj _ ι E w hw _).1 hv)
  · intro v hne heq
    have h4 := (placeConj _ ι E w hw (φ v)).2 (u v) ((h3 v _).2 rfl) hne heq
    have h5 := hφw v ⟨_, h4, by rw [InfinitePlace.mk_conjugate_eq, hφ]⟩
    exact hne ((h3 v w).1 h5).symm

end Places

section Rep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private noncomputable def mv {u : HeightOneSpectrum (𝓞 E)} (ψ : u.adicCompletion E →+* ℂ) (lam : DomWeight n) {d : ℕ}
    (e : Module.Basis (Fin d) ℂ (nablaSq ℂ n lam)) : finU E n →* Matrix (Fin d) (Fin d) ℂ where
  toFun g := LinearMap.toMatrix e e (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ (cLoc u g.1)))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    exact LinearMap.toMatrix_one e
  map_mul' a b := by
    simp only [MulMemClass.coe_mul, map_mul]
    exact LinearMap.toMatrix_mul e _ _

private theorem mv_apply {u : HeightOneSpectrum (𝓞 E)} (ψ : u.adicCompletion E →+* ℂ) (lam : DomWeight n) {d : ℕ}
    (e : Module.Basis (Fin d) ℂ (nablaSq ℂ n lam)) (g : finU E n) :
    mv ψ lam e g = LinearMap.toMatrix e e (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ (cLoc u g.1))) := rfl

private theorem expand {V : Type} [Fintype V] {W : V → Type} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
    {N : Type} [AddCommGroup N] [Module ℂ N] {d : V → ℕ} (f : MultilinearMap ℂ W N)
    (e : ∀ v, Module.Basis (Fin (d v)) ℂ (W v)) (T : ∀ v, W v →ₗ[ℂ] W v) (i : ∀ v, Fin (d v)) :
    f (fun v => T v (e v (i v))) =
      ∑ j : ∀ v, Fin (d v), (∏ v, LinearMap.toMatrix (e v) (e v) (T v) (j v) (i v)) • f (fun v => e v (j v)) := by
  have h : ∀ v, T v (e v (i v)) = ∑ b, LinearMap.toMatrix (e v) (e v) (T v) b (i v) • e v b := fun v => by
    simp only [LinearMap.toMatrix_apply]
    exact ((e v).sum_repr _).symm
  rw [show (fun v => T v (e v (i v))) = fun v => ∑ b, LinearMap.toMatrix (e v) (e v) (T v) b (i v) • e v b from funext h,
    MultilinearMap.map_sum]
  exact Finset.sum_congr rfl fun j _ => f.map_smul_univ _ _

private theorem inf_comm (k : infU E n) (g : finU E n) : k.1 * g.1 = g.1 * k.1 := by
  have h := GlobalTheory.BCT.TrKer.eq_splitFin_mul_splitInf (k.1 * g.1)
  have h1 : GlobalTheory.BCT.TrKer.splitFin E n (k.1 * g.1) = g := by
    rw [map_mul, GlobalTheory.BCT.TrKer.splitFin_inf, GlobalTheory.BCT.TrKer.splitFin_fin, one_mul]
  have h2 : GlobalTheory.BCT.TrKer.splitInf E n (k.1 * g.1) = k := by
    have a1 : GlobalTheory.BCT.TrKer.splitInf E n g.1 = 1 := by simpa using GlobalTheory.BCT.TrKer.splitInf_mul g 1
    have a2 : GlobalTheory.BCT.TrKer.splitInf E n k.1 = k := by simpa using GlobalTheory.BCT.TrKer.splitInf_mul 1 k
    rw [map_mul, a1, a2, mul_one]
  rw [h1, h2] at h
  exact h

private theorem cEmb_rat {γ₀ : GlobalTheory.BCT.UE E n} {r : UA E n} (hr : r ∈ ratU E n)
    (hre : ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ₀.1) (τ : E →+* ℂ) :
    cEmb τ r = GeneralLinearGroup.map τ γ₀.1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hr (k := r) rfl i j
  have h1 := hx (InfinitePlace.mk τ).embedding
  rw [hre] at h1
  have h2 : x = γ₀.1.val i j := ((InfinitePlace.mk τ).embedding.injective h1).symm
  rw [hx τ, h2]
  rfl

private theorem cLoc_finPt (γ₀ : GlobalTheory.BCT.UE E n) (u : HeightOneSpectrum (𝓞 E)) :
    cLoc u (GlobalTheory.BCT.finPt γ₀).1 = GeneralLinearGroup.map (algebraMap E (u.adicCompletion E)) γ₀.1 := by
  have h : cLoc u (GlobalTheory.BCT.finPt γ₀).1 = GeneralLinearGroup.map (pLoc E u) (GlobalTheory.BCT.FinPart.pU (GlobalTheory.BCT.finPt γ₀)) := rfl
  rw [h, GlobalTheory.BCT.FinPart.pU_finPt]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rfl

end Rep

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem F_ne {V : Type} [Fintype V] {lamv : V → DomWeight n} {φ : V → (E →+* ℂ)} {d : V → ℕ}
    (e : ∀ v, Module.Basis (Fin (d v)) ℂ (nablaSq ℂ n (lamv v)))
    (f : MultilinearMap ℂ (fun v => nablaSq ℂ n (lamv v)) (UA E n → ℂ)) (hf0 : f ≠ 0)
    (hinf : ∀ g ∈ infU E n, ∀ x, f (fun v => GlobalTheory.Branching.sqRep ℂ n (lamv v) (cEmb (φ v) g) (x v)) = RU E n g (f x)) :
    (fun (g : finU E n) (i : ∀ v, Fin (d v)) => f (fun v => e v (i v)) g.1) ≠ 0 := by
  intro h
  have h1 : ∀ (g : finU E n) x, f x g.1 = 0 := by
    intro g x
    have h2 : (LinearMap.proj g.1 : (UA E n → ℂ) →ₗ[ℂ] ℂ).compMultilinearMap f = 0 :=
      Module.Basis.ext_multilinear e fun i => congrFun (congrFun h g) i
    exact congrArg (fun m => m x) h2
  refine hf0 (MultilinearMap.ext fun x => funext fun g => ?_)
  have hg := GlobalTheory.BCT.TrKer.eq_splitFin_mul_splitInf g
  have h3 := congrFun (hinf _ (GlobalTheory.BCT.TrKer.splitInf E n g).2 x) (GlobalTheory.BCT.TrKer.splitFin E n g).1
  have h4 : RU E n (GlobalTheory.BCT.TrKer.splitInf E n g).1 (f x) (GlobalTheory.BCT.TrKer.splitFin E n g).1 = f x g := by
    conv_rhs => rw [hg]
    rfl
  rw [← h4, ← h3, h1]
  rfl

private theorem F_aut {V : Type} [Fintype V] {lamv : V → DomWeight n} {φ : V → (E →+* ℂ)}
    {u : V → HeightOneSpectrum (𝓞 E)} (ψ : ∀ v, (u v).adicCompletion E →+* ℂ)
    (hψ : ∀ v x, ψ v (algebraMap E _ x) = φ v x) {d : V → ℕ} [DecidableEq (∀ v, Fin (d v))]
    (e : ∀ v, Module.Basis (Fin (d v)) ℂ (nablaSq ℂ n (lamv v)))
    (f : MultilinearMap ℂ (fun v => nablaSq ℂ n (lamv v)) (UA E n → ℂ))
    (hleft : ∀ x, ∀ γ ∈ ratU E n, ∀ g, f x (γ * g) = f x g)
    (hinf : ∀ g ∈ infU E n, ∀ x, f (fun v => GlobalTheory.Branching.sqRep ℂ n (lamv v) (cEmb (φ v) g) (x v)) = RU E n g (f x))
    (γ : finU E n) (hγ : γ ∈ GlobalTheory.BCT.ratFinU E n) (g : finU E n) :
    (fun i : ∀ v, Fin (d v) => f (fun v => e v (i v)) (γ * g).1) =
      tens (fun v => mv (ψ v) (lamv v) (e v)) γ *ᵥ (fun i => f (fun v => e v (i v)) g.1) := by
  obtain ⟨γ₀, rfl⟩ := ((GlobalTheory.BCT.FinPart.finPt_props E n).2.2 γ).1 hγ
  obtain ⟨r, hr, hsf, hre⟩ := GlobalTheory.BCT.RatPt.ratPt E n γ₀
  set k := GlobalTheory.BCT.TrKer.splitInf E n r with hk
  have hrk : r = (GlobalTheory.BCT.finPt γ₀).1 * k.1 := by
    rw [← hsf]
    exact GlobalTheory.BCT.TrKer.eq_splitFin_mul_splitInf r
  have hm : ∀ v, GeneralLinearGroup.map (ψ v) (cLoc (u v) (GlobalTheory.BCT.finPt γ₀).1) = cEmb (φ v) k.1 := by
    intro v
    have h1 : cEmb (φ v) r = cEmb (φ v) k.1 := by
      rw [hrk, map_mul, GlobalTheory.BCT.TrKer.cEmb_fin, one_mul]
    rw [← h1, cEmb_rat hr hre, cLoc_finPt]
    exact Units.ext (Matrix.ext fun i j => hψ v _)
  have hmi : ∀ v, GeneralLinearGroup.map (ψ v) (cLoc (u v) ((GlobalTheory.BCT.finPt γ₀)⁻¹).1) = cEmb (φ v) (k⁻¹).1 := fun v => by
    have a1 : cLoc (u v) ((GlobalTheory.BCT.finPt γ₀)⁻¹).1 = (cLoc (u v) (GlobalTheory.BCT.finPt γ₀).1)⁻¹ := map_inv _ _
    have a2 : cEmb (φ v) (k⁻¹).1 = (cEmb (φ v) k.1)⁻¹ := map_inv _ _
    rw [a1, a2, map_inv, hm]
  funext i
  have hx : (GlobalTheory.BCT.finPt γ₀ * g).1 = r * ((k⁻¹).1 * g.1) := by
    have a3 : (k⁻¹).1 = k.1⁻¹ := rfl
    rw [hrk, a3, mul_assoc, mul_inv_cancel_left]
    rfl
  have key : f (fun v => e v (i v)) (GlobalTheory.BCT.finPt γ₀ * g).1 = RU E n (k⁻¹).1 (f fun v => e v (i v)) g.1 := by
    rw [hx, hleft _ r hr, inf_comm k⁻¹ g]
    rfl
  rw [key, ← hinf _ (k⁻¹).2,
    expand f e (fun v => GlobalTheory.Branching.sqRep ℂ n (lamv v) (cEmb (φ v) (k⁻¹).1)) i]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, tens_apply, mv_apply, hmi]

end Forms

section Core

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def RB {u : HeightOneSpectrum (𝓞 E)} (ψ : u.adicCompletion E →+* ℂ) (lam : DomWeight n) {d : ℕ}
    (e : Module.Basis (Fin d) ℂ (nablaSq ℂ n lam)) (C : ℝ) : Prop :=
  ∀ lo hi : ℤ, (∀ i, lo ≤ lam.w i ∧ lam.w i ≤ hi) → ∀ g : GL (Fin n) (u.adicCompletion E),
    (∀ i j, Valued.v (g.val i j) ≤ 1) → ∀ i j,
      nu ι (LinearMap.toMatrix e e (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ g)) i j) ≤
        C * nu ι (ψ g.val.det) ^ lo ∧
      nu ι (LinearMap.toMatrix e e (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ g⁻¹)) i j) ≤
        C * nu ι (ψ g.val.det) ^ (-hi)

private theorem core (hn : 1 ≤ n) (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (lam : (E →+* ℂ) → DomWeight n)
    (hlam : ∀ τ, HasWeightAt σ τ (lam τ)) (w : HeightOneSpectrum (𝓞 E)) (hw : IsSplitAt w) (hU : IsUnramU σ w)
    (lo hi : (E →+* ℂ) → ℤ) (hlh : ∀ τ i, lo τ ≤ (lam τ).w i ∧ (lam τ).w i ≤ hi τ) (s : Finset (UA E n)) (a : ℂ)
    (hs : ∀ f ∈ σ, (∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → RU E n y f = f) → ∑ x ∈ s, RU E n x f = a • f)
    (hsU : ∀ x ∈ s, x ∈ locU n w) (B : (E →+* ℂ) → ℝ) (hB : ∀ τ, 0 ≤ B τ)
    (hW : ∀ L : List (UA E n), (∀ x ∈ L, x ∈ s) → ∀ (u : HeightOneSpectrum (𝓞 E)), u = w → ∀ τ ∈ Ov ι w,
      ∀ ψ : u.adicCompletion E →+* ℂ, (∀ x : E, ψ (algebraMap E _ x) = τ x) → (∀ x, nu ι (ψ x) ≤ 1 ↔ Valued.v x ≤ 1) →
      ∀ (d : ℕ) (e : Module.Basis (Fin d) ℂ (nablaSq ℂ n (lam τ))) (C : ℝ), RB ι ψ (lam τ) e C → ∀ i j,
        nu ι (LinearMap.toMatrix e e (GlobalTheory.Branching.sqRep ℂ n (lam τ) (GeneralLinearGroup.map ψ (cLoc u L.prod⁻¹))) i j) ≤
          C * B τ ^ L.length) :
    nu ι a ≤ ∏ τ ∈ Ov ι w, B τ := by
  obtain ⟨φ, u, ψ, hφ, hψ, hint, hOv, hmk, hund⟩ := exists_places ι w hw
  obtain ⟨f, K, hf0, hfσ, hfinf, hKo, hKl, hKf, hwf⟩ :=
    vecForm E n hn σ hσ φ hφ (fun v => lam (φ v)) (fun v => hlam (φ v)) w hU
  let d : InfinitePlace E → ℕ := fun v => Module.finrank ℂ (nablaSq ℂ n (lam (φ v)))
  let e : ∀ v, Module.Basis (Fin (d v)) ℂ (nablaSq ℂ n (lam (φ v))) := fun v => Module.finBasis ℂ _
  have hrep := fun v => repBound _ ι E (u v) (ψ v) (fun x hx => (hint v x).2 hx) n (lam (φ v)) (d v) (e v)
  choose C0 hC0 hC using hrep
  have hRB : ∀ v, RB ι (ψ v) (lam (φ v)) (e v) (C0 v) := hC
  let D : InfinitePlace E → ℝ := fun v => max (C0 v) 1
  have hD1 : ∀ v, 1 ≤ D v := fun v => le_max_right _ _
  have hD0 : ∀ v, 0 ≤ D v := fun v => zero_le_one.trans (hD1 v)
  let M := fun v => mv (ψ v) (lam (φ v)) (e v)
  letI : DecidableEq (∀ v, Fin (d v)) := fun a b => Classical.propDecidable (a = b)
  let F : finU E n → (∀ v, Fin (d v)) → ℂ := fun g i => f (fun v => e v (i v)) g.1
  have hsF : ∀ x ∈ s, x ∈ finU E n := fun x hx => (Subgroup.mem_inf.1 (hsU x hx)).1
  have hleft : ∀ x, ∀ γ ∈ ratU E n, ∀ g, f x (γ * g) = f x g := fun x => (hσ.aut (f x) (hfσ x)).left
  have hinv : ∀ (u' : HeightOneSpectrum (𝓞 E)) (y : finU E n), cLoc u' (y⁻¹).1 = (cLoc u' y.1)⁻¹ :=
    fun _ _ => map_inv _ _
  have hKb : ∀ k ∈ K, ∀ i j, nu ι (tens M k i j) ≤ ∏ v, D v := by
    intro k hk i j
    rw [tens_apply, nu_prod]
    refine Finset.prod_le_prod (fun _ _ => nu_nonneg _ _) fun v _ => ?_
    have hg := intDet_of_KGL (hKl k hk (u v))
    have h0 : nu ι (ψ v (cLoc (u v) k.1).val.det) = 1 := by
      have h1 := nu_of_val ι (u v) (ψ v) (φ v) (hψ v) (hint v) _ 0 hg.2
      simpa using h1
    have h2 := (hRB v (lo (φ v)) (hi (φ v)) (hlh _) _ hg.1 (j v) (i v)).2
    rw [h0, _root_.one_zpow, mul_one] at h2
    simp only [M, mv_apply, hinv]
    exact h2.trans (le_max_left _ _)
  have himg : Ov ι w = (Finset.univ.filter fun v => u v = w).image φ := by
    ext τ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hτ
      exact ⟨InfinitePlace.mk τ, (hOv _).1 (by rw [hmk τ hτ]; exact hτ), hmk τ hτ⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hOv v).2 hv
  have hinj : Function.Injective φ := fun a b h => by rw [← hφ a, ← hφ b, h]
  have hprod : ∀ m : ℕ, (∏ τ ∈ Ov ι w, B τ) ^ m = ∏ v, if u v = w then B (φ v) ^ m else 1 := by
    intro m
    rw [← Finset.prod_pow, himg, Finset.prod_image hinj.injOn, Finset.prod_filter]
  have hLb : ∀ L : List (finU E n), (∀ x ∈ L, x ∈ s.subtype (· ∈ finU E n)) → ∀ i j,
      nu ι (tens M L.prod i j) ≤ (∏ v, D v) * (∏ τ ∈ Ov ι w, B τ) ^ L.length := by
    intro L hL i j
    have hL' : ∀ x ∈ L.map Subtype.val, x ∈ s := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact Finset.mem_subtype.1 (hL y hy)
    have hp : (L.prod).1 = (L.map Subtype.val).prod := map_list_prod (finU E n).subtype L
    have hloc : (L.prod).1 ∈ locU n w := by
      rw [hp]
      exact Subgroup.list_prod_mem _ fun x hx => hsU x (hL' x hx)
    rw [tens_apply, nu_prod, hprod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => nu_nonneg _ _) fun v _ => ?_
    by_cases h : u v = w
    · have h1 := hW _ hL' (u v) h (φ v) ((hOv v).2 h) (ψ v) (hψ v) (hint v) (d v) (e v) (C0 v) (hRB v) (j v) (i v)
      rw [← hp, List.length_map] at h1
      rw [if_pos h]
      simp only [M, mv_apply, hinv]
      refine (by simpa only [map_inv] using h1 : _ ≤ C0 v * B (φ v) ^ L.length).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hB _) _)
    · have h1 : cLoc (u v) (L.prod).1 = 1 := by
        have h2 := (Subgroup.mem_inf.1 hloc).2
        rw [Subgroup.mem_iInf] at h2
        have h3 := h2 (u v)
        rw [Subgroup.mem_iInf] at h3
        exact MonoidHom.mem_ker.1 (h3 (hund v h))
      rw [if_neg h, mul_one]
      simp only [M, mv_apply, hinv, h1, inv_one, map_one]
      rw [show (1 : Module.End ℂ _) = LinearMap.id from rfl, LinearMap.toMatrix_id, Matrix.one_apply]
      split_ifs
      · rw [nu_one]
        exact hD1 v
      · rw [nu_zero]
        exact hD0 v
  refine absBound _ ι (finU E n) (GlobalTheory.BCT.ratFinU E n) K (∀ v, Fin (d v)) (tens M) F (s.subtype (· ∈ finU E n)) a
    (∏ τ ∈ Ov ι w, B τ) (∏ v, D v) (Finset.prod_nonneg fun τ _ => hB τ)
    (GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen E n K hKo) (F_ne e f hf0 hfinf)
    (fun γ hγ g => F_aut ψ hψ e f hleft hfinf γ hγ g) ?_ ?_ hKb hLb
  · intro k hk g
    funext i
    exact congrFun (hKf k hk _) g.1
  · intro g
    funext i
    have h1 := congrFun (hs (f fun v => e v (i v)) (hfσ _) fun y h1 h2 => hwf y h1 h2 _) g.1
    rw [Finset.sum_apply] at h1
    rw [Finset.sum_apply]
    exact (Finset.sum_subtype_of_mem (fun x => RU E n x (f fun v => e v (i v)) g.1) hsF).trans h1

end Core

section Words2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem intDet_prod {w : HeightOneSpectrum (𝓞 E)} {j : ℕ} (L : List (UA E n))
    (h : ∀ x ∈ L, IntDet w j (cLoc w x)) : IntDet w (j * L.length) (cLoc w L.prod) := by
  induction L with
  | nil => simpa using intDet_one w
  | cons x L ih =>
    have h1 := intDet_mul (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.prod_cons, map_mul, List.length_cons, Nat.mul_succ, Nat.add_comm]
    exact h1

private theorem intDet_prod_inv {w : HeightOneSpectrum (𝓞 E)} {j : ℕ} (L : List (UA E n))
    (h : ∀ x ∈ L, IntDet w j (cLoc w x⁻¹)) : IntDet w (j * L.length) (cLoc w L.prod⁻¹) := by
  induction L with
  | nil => simpa using intDet_one w
  | cons x L ih =>
    have h1 := intDet_mul (ih fun y hy => h y (List.mem_cons_of_mem _ hy)) (h x List.mem_cons_self)
    rw [List.prod_cons, _root_.mul_inv_rev, map_mul, List.length_cons, Nat.mul_succ]
    exact h1

private theorem zpow_pow_pow (x : ℝ) (z : ℤ) (j m : ℕ) : ((x ^ z) ^ j) ^ m = (x ^ (j * m)) ^ z := by
  rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

end Words2

end UpperTheory.V.Z.Int

theorem UpperTheory.V.Z.Int.opBound :
    UpperTheory.V.Z.Int.OpBound := by
  intro l _ ι E _ _ _ n hn σ hσ lam hlam w hw hU lo hi hlh j s a hs
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Finset.prod_pow]
    refine core ι hn σ hσ lam hlam w hw hU lo hi hlh s a hs (fun x hx => (h x hx).1) _
      (fun τ => pow_nonneg (zpow_nonneg (nu_nonneg ι _) _) _) ?_
    intro L hL u hu τ _ ψ hψ hint d e C hR a b
    subst hu
    have hI : IntDet u (j * L.length) (cLoc u L.prod) := intDet_prod L fun x hx => (h x (hL x hx)).2
    have hb := (hR (lo τ) (hi τ) (hlh τ) (cLoc u L.prod) hI.1 a b).2
    rw [nu_of_val ι u ψ τ hψ hint _ _ hI.2] at hb
    rw [map_inv, zpow_pow_pow]
    exact hb
  · rw [← Finset.prod_pow]
    refine core ι hn σ hσ lam hlam w hw hU lo hi hlh s a hs
      (fun x hx => (h x hx).1) _
      (fun τ => pow_nonneg (zpow_nonneg (nu_nonneg ι _) _) _) ?_
    intro L hL u hu τ _ ψ hψ hint d e C hR a b
    subst hu
    have hI : IntDet u (j * L.length) (cLoc u L.prod⁻¹) := intDet_prod_inv L fun x hx => (h x (hL x hx)).2
    have hb := (hR (lo τ) (hi τ) (hlh τ) (cLoc u L.prod⁻¹) hI.1 a b).1
    rw [nu_of_val ι u ψ τ hψ hint _ _ hI.2] at hb
    rw [zpow_pow_pow]
    exact hb
