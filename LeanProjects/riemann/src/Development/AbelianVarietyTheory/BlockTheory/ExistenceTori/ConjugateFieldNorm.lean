import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct

section Adelic

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]

def cjF : E →ₐ[F] E :=
  { (IsCMField.complexConj E : E →+* E) with
    commutes' := fun x => by
      have h : algebraMap F E x ∈ maximalRealSubfield E := by
        rw [mem_maximalRealSubfield_iff]
        intro φ
        exact RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))) x
      exact (IsCMField.complexConj E).commutes ⟨_, h⟩ }

abbrev Af : Type := FiniteAdeleRing (𝓞 F) F

abbrev Ai : Type := InfiniteAdeleRing F

structure HSpace (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) where
  Gm : Matrix (Fin r) (Fin r) E
  Gm_herm : ∀ a b, cc (Gm a b) = Gm b a
  Gm_det : Gm.det ≠ 0
  L : Submodule (𝓞 E) (Fin r → E)
  L_fg : L.FG
  L_span : Submodule.span E (L : Set (Fin r → E)) = ⊤
  L_dual : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gm x y)

def HSpace.std (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) : HSpace E r where
  Gm := 1
  Gm_herm a b := by by_cases h : a = b <;> simp [cc, Matrix.one_apply, h, eq_comm]
  Gm_det := by simp
  L := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
  L_fg := Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  L_span := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (x i) : Fin r → E) = x i • (Pi.single i 1 : Fin r → E) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span fun k _ => ?_)
    by_cases h : k = i
    · subst h; simpa using Submodule.one_le.1 le_rfl
    · simp [h]
  L_dual x := by
    have hi : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z => by
      rw [Submodule.mem_one]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
    have hh : ∀ y, herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := fun y => by
      simp [herm, Matrix.one_apply]
    constructor
    · intro hx y hy
      rw [hh]
      refine IsIntegral.sum _ fun a _ => ((hi _).1 (hx a trivial)).mul ?_
      exact ((hi _).1 (hy a trivial)).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
    · intro h a _
      have := h (Pi.single a 1) fun k _ => by
        by_cases hk : k = a
        · subst hk; simpa using Submodule.one_le.1 le_rfl
        · simp [hk]
      rw [hh, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc]) (by simp)] at this
      exact (hi _).2 (by simpa [cc] using this)

variable {r : ℕ}

def HSpace.HasSig (V : HSpace E r) (p : ℕ) : Prop :=
  p ≤ r ∧ ∀ τ : E →+* ℂ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
    gram τ V.Gm P = Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)

variable (A : Type) [CommRing A] [Algebra F A]

def incl : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom

def hermA (V : HSpace E r) (x y : Fin r → A ⊗[F] E) : A ⊗[F] E :=
  ∑ a, ∑ b, x a * incl F A (V.Gm a b) * Algebra.TensorProduct.map (AlgHom.id F A) (cjF F) (y b)

def UA (V : HSpace E r) : Subgroup (GL (Fin r) (A ⊗[F] E)) where
  carrier := {g | ∀ x y, hermA F A V (g.val.mulVec x) (g.val.mulVec y) = hermA F A V x y}
  one_mem' := fun x y => by simp
  mul_mem' := fun {g h} hg hh x y => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := fun {g} hg x y => by
    rw [← hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.one_mulVec]

abbrev GA (V : HSpace E r) : Type := UA F (Ai F) V × UA F (Af F) V

def IsRat (V : HSpace E r) (γ : GL (Fin r) E) (g : GA F V) : Prop :=
  g.1.1.val = γ.val.map (incl F (Ai F)) ∧ g.2.1.val = γ.val.map (incl F (Af F))

def latHat (L : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → Af F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ L, z = fun i => a ⊗ₜ[F] x i}

def levelK (V : HSpace E r) (N : ℕ) : Subgroup (GA F V) where
  carrier := {k | k.1 = 1 ∧ (∀ z, z ∈ latHat F V.L ↔ k.2.1.val.mulVec z ∈ latHat F V.L) ∧
    ∀ z ∈ latHat F V.L, ∃ w ∈ latHat F V.L, k.2.1.val.mulVec z - z = N • w}
  one_mem' := ⟨rfl, fun z => by simp, fun z _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    have e : ∀ z, (g * h).2.1.val.mulVec z = g.2.1.val.mulVec (h.2.1.val.mulVec z) := fun z => by
      rw [Matrix.mulVec_mulVec]; rfl
    refine ⟨by rw [Prod.fst_mul, g1, h1, mul_one], fun z => by rw [e, ← g2, ← h2], fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := h3 z hz
    obtain ⟨w', hw', e2⟩ := g3 _ ((h2 z).1 hz)
    exact ⟨w' + w, add_mem hw' hw, by rw [e, smul_add, ← e1, ← e2]; abel⟩
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    have e : ∀ z, g.2.1.val.mulVec ((g⁻¹).2.1.val.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec]
      have : g.2.1.val * (g⁻¹).2.1.val = 1 := Units.mul_inv _
      rw [this, Matrix.one_mulVec]
    have s : ∀ z, z ∈ latHat F V.L ↔ (g⁻¹).2.1.val.mulVec z ∈ latHat F V.L := fun z => by
      rw [g2 ((g⁻¹).2.1.val.mulVec z), e]
    refine ⟨by rw [Prod.fst_inv, g1, inv_one], s, fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := g3 _ ((s z).1 hz)
    exact ⟨-w, neg_mem hw, by rw [smul_neg, ← e1, e]; abel⟩

def LevelByCongruence (V : HSpace E r) (N : ℕ) : Prop :=
  ∀ k : GA F V, k ∈ levelK F V N ↔
    k.1 = 1 ∧ ∀ z ∈ latHat F V.L, ∃ w ∈ latHat F V.L, k.2.1.val.mulVec z - z = N • w

def latAt (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (V : HSpace E r) (g : UA F (Af F) V) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x : Fin r → E,
    (∃ z ∈ latHat F V.L, (fun i => incl F (Af F) (x i)) = g.1.val.mulVec z) ∧ v = a • x}

def IsArch (τ : E →+* ℂ) (th : Ai F ⊗[F] E →+* ℂ) : Prop :=
  (Continuous fun a : Ai F => th (a ⊗ₜ[F] 1)) ∧ ∀ x, th (incl F (Ai F) x) = τ x

end Adelic

structure Nums (E : Type) [Field E] [NumberField E] where
  k : ℕ
  m : ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  Nc : ℕ
  Nc_pos : 0 < Nc
  AA : FractionalIdeal (nonZeroDivisors (𝓞 E)) E
  Os : Subring ℂ

example (E : Type) [Field E] [NumberField E] : Nums E :=
  ⟨2, 2, ![3, 5], fun i => by fin_cases i <;> norm_num, by decide, 1, one_pos, 1, ⊥⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Nums.r (R : Nums E) : ℕ := R.k + R.m - 1

abbrev Nums.J (R : Nums E) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

def Nums.p (R : Nums E) (j : R.J) : ℕ := R.k + j.1 - 1

def Nums.q (R : Nums E) (j : R.J) : ℕ := R.m - j.1

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E]

structure CorePar (R : Nums E) : Type 1 where
  H : Host E
  l : Level H
  c : Coeff l
  Dw : R.J → Datum H
  Xo : ∀ j, Moduli (Dw j) l

  U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ R.r

  V : R.J → HSpace E R.r

  dict : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → Σ k, Frame ((U j σ).X k).Ψ R.r

  mu : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → ℂ

  Kf : ∀ j, Subgroup (GA F (V j))

  pi : Fin 2 → 𝓞 E

namespace CorePar

variable {F} {R : Nums E} (Q : CorePar F R)

def xi0 : E := -1 / ((R.Nc : E) * (Q.H.rt : E))

def xiAbs : ℝ := 1 / ((R.Nc : ℝ) * Real.sqrt Q.H.d)

theorem norm_embedding_hostFormConstant_eq (τ : E →+* ℂ) : ‖τ Q.xi0‖ = Q.xiAbs := by
  have h : τ (Q.H.rt : E) ^ 2 = -(Q.H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => τ (x : E)) Q.H.rt_sq
    simpa using this
  have h2 : ‖τ (Q.H.rt : E)‖ = Real.sqrt Q.H.d := by
    rw [← Real.sqrt_sq (norm_nonneg (τ (Q.H.rt : E))), ← norm_pow, h]; simp
  simp [xi0, xiAbs, h2]

def sg0 : Q.c.F →+* ℂ := Q.c.F.val.toRingHom

theorem base_embedding_good : GoodEmb Q.c Q.sg0 := rfl

def PinBase : Prop :=
  Module.finrank F E = 2 ∧
  Q.H.rt0 = Complex.I * (Real.sqrt Q.H.d : ℝ) ∧
  (∀ x : E, x ∈ R.AA ↔ ∀ a ∈ R.AA, Algebra.trace ℚ E (Q.xi0 * x * cc a) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
  Q.l.M = R.g 0 * R.g 1 ∧ Q.l.A = 1 ∧
  (∀ i, Q.pi i ∈ Algebra.adjoin ℤ {Q.H.w0} ∧ Q.pi i * Q.H.bar (Q.pi i) = (R.g i : 𝓞 E)) ∧
  Q.l.Mb = Ideal.span {Q.H.bar (Q.pi 0) * Q.H.bar (Q.pi 1)} ∧
  ∀ z : ℂ, z ∈ R.Os ↔ ∃ x : 𝓞 Q.c.F, Q.sg0 (x : Q.c.F) = z

def PinSpace (j : R.J) : Prop :=
  (Q.V j).HasSig (R.p j) ∧ (Q.Dw j).p = R.p j ∧ (Q.Dw j).q = R.q j ∧
  (∃ φ : (Q.Dw j).La →ₗ[𝓞 E] (Fin R.r → E), Function.Injective φ ∧
    LinearMap.range φ = latAt F R.AA (Q.V j) 1 ∧
    ∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-Q.xi0 * herm (Q.V j).Gm (φ x) (φ y))) ∧
  Q.Kf j = levelK F (Q.V j) (R.g 0 * R.g 1)

def PinDict (j : R.J) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) : Prop :=
  IsUnf (Q.U j σ) ∧
  ∃ (gk : (Q.U j σ).Comp → UA F (Af F) (Q.V j)) (x0 : ∀ k, Frame ((Q.U j σ).X k).Ψ R.r)
    (th : (E →+* ℂ) → (Ai F ⊗[F] E →+* ℂ)), (∀ τ, IsArch F τ (th τ)) ∧
    (∀ k, ((Q.U j σ).X k).Gm = -(Q.V j).Gm ∧ ((Q.U j σ).X k).ξ0 = -Q.xi0 ∧
      (∀ la, ∀ γ ∈ ((Q.U j σ).X k).Γ, ((Q.U j σ).X k).χ la γ = 1) ∧
      ((Q.U j σ).X k).Λ = latAt F R.AA (Q.V j) (gk k) ∧
      (∀ γ, γ ∈ ((Q.U j σ).X k).Γ ↔ ∃ g : GA F (Q.V j), IsRat F (Q.V j) γ g ∧
        ((1, (gk k)⁻¹ * g.2 * gk k) : GA F (Q.V j)) ∈ Q.Kf j) ∧
      x0 k ∈ ((Q.U j σ).X k).dom ∧ ∀ τ i, ‖dmin ((Q.U j σ).X k).Gm (x0 k) τ i‖ = 1) ∧
    ∀ h : GA F (Q.V j), ∃ (γ : GL (Fin R.r) E) (g : GA F (Q.V j)), IsRat F (Q.V j) γ g ∧
      ((1, (gk (Q.dict j σ hσ h).1)⁻¹ * (g * h).2) : GA F (Q.V j)) ∈ Q.Kf j ∧
      ∀ τ, mat (Q.dict j σ hσ h).2 τ = ((g * h).1.1.val.map (th τ.1)) * mat (x0 (Q.dict j σ hσ h).1) τ

def PinMu (j : R.J) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) : Prop :=
  (∀ g g', Q.mu j σ hσ (g * g') = Q.mu j σ hσ g * Q.mu j σ hσ g') ∧ (∀ g, ‖Q.mu j σ hσ g‖ = 1) ∧
  (∀ γ g, IsRat F (Q.V j) γ g → Q.mu j σ hσ g = 1) ∧
  ∀ g : GA F (Q.V j), g.1.1.val.det = 1 → g.2.1.val.det = 1 → Q.mu j σ hσ g = 1

def Pins : Prop := Q.PinBase ∧ ∀ j, Q.PinSpace j ∧ ∀ σ hσ, Q.PinDict j σ hσ ∧ Q.PinMu j σ hσ

abbrev Rules (j : R.J) : Type := Rul (Q.Xo j) Q.c

def Cusp (j : R.J) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule Q.c.F (Q.Rules j) := cusp (Q.Xo j) Q.c (Q.U j) a n

def supAt (j : R.J) (σ : Q.c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Q.Cusp j a n) : ℝ :=
  supC (Q.Xo j) Q.c (Q.U j) Q.xiAbs (goodOf Q.c σ) a n f

abbrev X0 (j : R.J) : (Q.U j Q.sg0).Comp → Data E R.r := (Q.U j Q.sg0).X

def frI (_Q : CorePar F R) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := 1

abbrev Cu (j : R.J) : Type := FJ.CuF (Q.X0 j) (min (R.p j) (R.q j))

def Xc (j : R.J) (cu : Q.Cu j) : Submodule (𝓞 E) (Fin (min (R.p j) (R.q j)) → E) := FJ.XcF (Q.X0 j) Q.frI cu

def Pt (j : R.J) (la : HeightOneSpectrum (𝓞 Q.c.F)) : Type :=
  PtV (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) Unit (fun _ _ _ _ => True) la

def vAt_vw {j : R.J} {la : HeightOneSpectrum (𝓞 Q.c.F)} (y : Q.Pt j la) (f : Q.Rules j) : EReal := vAtV y f

def nrm {j : R.J} {la : HeightOneSpectrum (𝓞 Q.c.F)} (y : Q.Pt j la) (f : Q.Rules j) : ℝ := nrmOf la (Q.vAt_vw y f)

theorem nrm_le_one_iff {j : R.J} {la : HeightOneSpectrum (𝓞 Q.c.F)} (y : Q.Pt j la) (f : Q.Rules j) :
    Q.nrm y f ≤ 1 ↔ 0 ≤ Q.vAt_vw y f := nrmOf_le_one_iff la (vAtV_ne_bot y f)

def adelFn (j : R.J) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) : Q.Rules j →ₛₗ[σ] (GA F (Q.V j) → ℂ) where
  toFun f g := Q.mu j σ hσ g * rdU (Q.U j σ) f (Q.dict j σ hσ g).1 (Q.dict j σ hσ g).2
  map_add' f f' := by funext g; rw [map_add]; exact mul_add _ _ _
  map_smul' a f := by funext g; rw [map_smulₛₗ]; exact mul_left_comm _ _ _

def adel0 (j : R.J) : Q.Rules j →ₛₗ[Q.sg0] (GA F (Q.V j) → ℂ) := Q.adelFn j Q.sg0 Q.base_embedding_good

def XiAbsModels : Prop := ∀ j σ, GoodEmb Q.c σ → ∀ k (τ : E →+* ℂ), ‖τ ((Q.U j σ).X k).ξ0‖ = Q.xiAbs

theorem xiAbsModels_of_pins (h : Q.Pins) : Q.XiAbsModels := by
  intro j σ hσ k τ
  obtain ⟨_, gk, x0, th, _, h2, _⟩ := ((h.2 j).2 σ hσ).1
  rw [(h2 k).2.1, map_neg, norm_neg, norm_embedding_hostFormConstant_eq]

end CorePar

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
