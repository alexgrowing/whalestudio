import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cF (D : D7) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

def latC (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.map ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))

def IsRat (V : HSp D) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E) : Prop :=
  matHom V γ = Formalism.UG.bc (incA D) γ'

def FinCong (V : HSp D) (N : ℕ) (k : GA D V) : Prop :=
  ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

structure IotaOK (Dw : Datum H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop where
  rt : (H.rt : D.host.E) = D.host.sqrtMinusD
  rt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD
  emb : LatEmb V ι
  isom : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

variable {Dw : Datum H} {l : Level H}

structure Ctx (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) : Type 1 where
  hr : V.rank = r
  g : ℕ
  e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  M : GlobalTheory.FrameUnif.ModelsOf F r
  ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)
  θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)
  x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ

namespace Ctx

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ} (C : Ctx Xo c σ V r)

structure OK : Prop where
  iota : IotaOK Dw V C.ι
  pos : 1 ≤ Dw.p + Dw.q
  lA : l.A = 1
  good : GoodEmb c σ
  base : GlobalTheory.FrameUnif.ModelBase C.M
  modelW : ∀ k, ModelW V C.hr (C.M.X k)
  inf : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (C.θ τ)
  orth : ∀ k, IsOrthogonalFrame (C.M.X k) C.x₀

def th : ∀ k, (C.M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun _ τ => C.θ τ.1

def Mark (h : GA D V) (k : Fin C.F.n) (γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((C.M.X k).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast C.hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((C.M.φ k (C.F.t k a) : Fin r → D.host.E) ∘ Fin.cast C.hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (C.ι a)) = (l.M : ℕ) • w

def fr (h : GA D V) (k : Fin C.F.n) : Frame (C.M.X k).Ψ r :=
  fun τ => (Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) h) * C.x₀ τ.1 :
    Matrix (Fin r) (Fin r) ℂ)

def IsDict (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) : Prop :=
  (∀ h, ∃ γ, C.Mark h (dict h).1 γ ∧ (dict h).2 = C.fr (γ * h) (dict h).1) ∧
    ∀ k, ∃ h, dict h = ⟨k, C.fr 1 k⟩

def unf (un : ∀ k, (C.M.X k).dom → FrPt Xo c (CAt σ)) : Unf Xo c σ r where
  Comp := Fin C.F.n
  X := C.M.X
  un := un

end Ctx

structure PkgLaws {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (Kf : Subgroup (GA D V)) (χ : (AE D)ˣ →* Circle)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop where
  unf : IsUnf U
  unTest : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)
  chi1 : ∀ k la γ, (U.X k).χ la γ = 1
  modelW : ∀ k, ModelW V hr (U.X k)
  familyUniformisationBasePointOrthogonal : ∀ k, IsOrthogonalFrame (U.X k) x₀
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  muVal : MuVal V χ mu
  adelAut : ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), IsHolCusp U.X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)
  expo : ∀ ρ, FJ.LatZ U.X ρ ∧ FJ.ExpoMatch U.X 1 ρ l.M
  dictLaws : ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr ∧
      DictLat U V hr dict ι e F ik φ th x₀

theorem cF_apply_eq_complexConj (D : D7) (x : D.host.E) : cF D x = IsCMField.complexConj D.host.E x := rfl

theorem mem_latC_iff_symm_mem (V : HSp D) (v : Fin V.rank → D.host.E) :
    v ∈ latC V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro hv
    exact ⟨_, hv, V.frame.equivFun.apply_symm_apply v⟩

theorem coe_selfDualLatticeInFrameCoordinates_eq (V : HSp D) : (latC V : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  ext v
  rw [SetLike.mem_coe, mem_latC_iff_symm_mem, Module.Basis.equivFun_symm_apply]
  rfl

theorem isLevelK_iff_finCong (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) :
    IsLevelK V N Kf ↔ ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ FinCong V N k := Iff.rfl

theorem isRat_one_one (V : HSp D) : IsRat V 1 1 := by
  unfold IsRat
  rw [map_one, map_one]

theorem exists_isRat_of_mem_GQ (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) : ∃ γ', IsRat V γ γ' := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ', e.symm⟩

theorem trace_model_eq_trace_hT (V : HSp D) {r : ℕ} (hr : V.rank = r) (u v : Fin V.rank → D.host.E) :
    Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (GlobalTheory.RecDict.gmW V hr) (u ∘ Fin.cast hr.symm) (v ∘ Fin.cast hr.symm)) =
    -Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm v) (V.frame.equivFun.symm u)) := by
  subst hr
  have h : herm (GlobalTheory.RecDict.gmW V rfl) (u ∘ Fin.cast rfl) (v ∘ Fin.cast rfl) =
      -V.hT (V.frame.equivFun.symm v) (V.frame.equivFun.symm u) := by
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
      herm, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    show u a * (-V.gram b a) * cc (v b) = -(u a * (cc (v b) * V.gram b a))
    ring
  rw [h, neg_neg, mul_neg, map_neg]

theorem isom_iff_model (Dw : Datum H) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) :
    (∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))) ↔
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (GlobalTheory.RecDict.gmW V hr) (ι x ∘ Fin.cast hr.symm) (ι y ∘ Fin.cast hr.symm)) := by
  have halt : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = -((Dw.EF y x : ℤ) : ℚ) := fun x y => by
    have h := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at h
    have h' : Dw.EF x y = -Dw.EF y x := by linarith
    rw [h', Int.cast_neg]
  simp only [trace_model_eq_trace_hT]
  constructor
  · intro h x y
    rw [halt, h]
  · intro h x y
    rw [halt, h, neg_neg]

namespace Ctx

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ} (C : Ctx Xo c σ V r)

theorem ok_iff_recOK : C.OK ↔ GlobalTheory.RecDict.RecOK C.M V C.hr C.ι C.th C.x₀ ∧
    (H.rt : D.host.E) = D.host.sqrtMinusD ∧ H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧ 1 ≤ Dw.p + Dw.q ∧ l.A = 1 ∧
    GoodEmb c σ ∧ ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (C.θ τ) := by
  constructor
  · intro h
    exact ⟨⟨h.base, h.modelW, h.iota.emb, (isom_iff_model Dw V C.hr C.ι).1 h.iota.isom, fun _ τ => h.inf τ.1,
      h.orth⟩, h.iota.rt, h.iota.rt0, h.pos, h.lA, h.good, h.inf⟩
  · rintro ⟨⟨h1, h2, h3, h4, -, h6⟩, k1, k2, k3, k4, k5, k6⟩
    exact ⟨⟨k1, k2, h3, (isom_iff_model Dw V C.hr C.ι).2 h4⟩, k3, k4, k5, h1, h2, k6, h6⟩

theorem markSpec_iff_mark (h : GA D V) (p : Σ k, Frame (C.M.X k).Ψ r) :
    GlobalTheory.RecDict.MarkSpec C.M V C.hr C.ι C.th C.x₀ h p ↔ ∃ γ, C.Mark h p.1 γ ∧ p.2 = C.fr (γ * h) p.1 := by
  constructor
  · rintro ⟨γ, h1, h2, h3, h4⟩
    exact ⟨γ, ⟨h1, h2, h3⟩, funext h4⟩
  · rintro ⟨γ, ⟨h1, h2, h3⟩, h4⟩
    exact ⟨γ, h1, h2, h3, fun τ => congrFun h4 τ⟩

theorem isDict_iff_markSpec (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) :
    C.IsDict dict ↔ (∀ h, GlobalTheory.RecDict.MarkSpec C.M V C.hr C.ι C.th C.x₀ h (dict h)) ∧
      ∀ k, ∃ h, dict h = ⟨k, C.fr 1 k⟩ := by
  simp only [IsDict, markSpec_iff_mark]

theorem unf_eq_toPj (un : ∀ k, (C.M.X k).dom → FrPt Xo c (CAt σ)) :
    C.unf un = (GlobalTheory.FrameUnif.unfOf C.e C.F C.M un).toPj := rfl

theorem mat_fr_one (k : Fin C.F.n) (τ : (C.M.X k).Ψ) : mat (C.fr 1 k) τ = C.x₀ τ.1 := by
  have h : archM V (C.θ τ.1) 1 = 1 := by
    unfold archM
    rw [map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  show Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) 1) * C.x₀ τ.1 = _
  rw [h]
  simp

end Ctx

example (V : HSp D) (N : ℕ) : FinCong V N 1 := fun z _ => ⟨0, zero_mem _, by simp⟩

example (D : D7) (x : D.host.E) : cF D (cF D x) = x := star_star x

example (D : D7) : cF D D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [cF_apply_eq_complexConj, IsCMField.complexEmbedding_complexConj, map_neg, hφ]
  simp

end GlobalTheory.Member
