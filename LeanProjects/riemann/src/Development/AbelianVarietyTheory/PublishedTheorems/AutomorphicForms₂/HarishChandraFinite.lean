import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.Published

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace AutFin

def coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ {f | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun k => ℓ (ρ k w)}

def IsContRep {K W : Type} [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) : Prop :=
  ∀ (ℓ : Module.Dual ℂ W) (w : W), Continuous fun k => ℓ (ρ k w)

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

def IsFrameFam (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ τ, IsUnit (fr τ) ∧ (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ

def kAt (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (k : Formalism.REAL.KG e) :
    GA D V :=
  atTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P)

def HasTypeAt (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (φ : GA D V → ℂ) : Prop :=
  ∀ x : GA D V, (fun k => φ (x * kAt θ V τ e P k)) ∈ coeffSpan ρ

def forms (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)]
    [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) :
    Set (GA D V → ℂ) :=
  {φ | IsAutFunSm θ V φ ∧ (∀ u ∈ U, u ∈ GfC V → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) ∧ ∀ τ k, gelf θ V τ k φ = c τ k • φ}

end AutFin

open AutFin in

def HarishChandraFinite : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) →
  ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsFrameFam V ε fr →
  ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) →
  ∀ c : D.what₂.Tau → ℕ → ℂ,
    FiniteDimensional ℂ (Submodule.span ℂ (forms θ V U ε fr ρ c))

namespace AutFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem conj_mem_UH {n : ℕ} {e : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm e * P = G) (k : Formalism.REAL.KG e) :
    P⁻¹ * Formalism.REAL.toMK k * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk : (Formalism.REAL.toMK k)ᴴ * Formalism.REAL.Jm e * Formalism.REAL.toMK k = Formalism.REAL.Jm e := (k : Formalism.REAL.UJ e).2
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
  change (P⁻¹ * Formalism.REAL.toMK k * P)ᴴ * G * (P⁻¹ * Formalism.REAL.toMK k * P) = G
  calc (P⁻¹ * Formalism.REAL.toMK k * P)ᴴ * G * (P⁻¹ * Formalism.REAL.toMK k * P)
      = Pᴴ * ((Formalism.REAL.toMK k)ᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm e * (P * P⁻¹) * Formalism.REAL.toMK k) * P := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]

open Classical in

theorem isAtTau_kAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k : Formalism.REAL.KG e) : IsAtTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P) (kAt θ V τ e P k) := by
  obtain ⟨g, hg, h1⟩ := ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.1
    (Function.update (fun _ => 1) τ (P⁻¹ * Formalism.REAL.toMK k * P)) (fun τ' => by
      by_cases c : τ' = τ
      · subst c; rw [Function.update_self]; exact conj_mem_UH hP h k
      · rw [Function.update_of_ne c]
        change (1 : Matrix _ _ ℂ)ᴴ * _ * 1 = _
        rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  have hex : ∃ x, IsAtTau θ V τ (P⁻¹ * Formalism.REAL.toMK k * P) x :=
    ⟨g, hg, by rw [h1, Function.update_self], fun τ' c => by rw [h1, Function.update_of_ne c]⟩
  rw [kAt, atTau, dif_pos hex]
  exact hex.choose_spec

theorem hasTypeAt_of_map (τ : D.what₂.Tau) (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W) (T : W →ₗ[ℂ] (GA D V → ℂ))
    (hT : ∀ k w, T (ρ k w) = rTr V (kAt θ V τ e P k) (T w)) (w : W) : HasTypeAt θ V τ e P ρ (T w) := fun x =>
  Submodule.subset_span ⟨(LinearMap.proj x).comp T, w, funext fun k => (congrFun (hT k w) x).symm⟩

theorem exists_isFrameFam (hV : V.SigOK) : ∃ ε fr, IsFrameFam V ε fr := by
  have key : ∀ τ, ∃ (e : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsUnit P ∧ Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ := by
    intro τ
    obtain ⟨hpq, ⟨A, hA⟩, hB⟩ := GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D τ))
    obtain ⟨B, hAB, -⟩ := hB A hA
    let s := (finSumFinEquiv.trans (finCongr hpq)).symm
    have hJ : Formalism.REAL.Jm (fun i => (s i).isLeft) = (Formalism.UG.Jpq _ _).submatrix s s := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Formalism.REAL.Jm, diagonal_apply_eq, submatrix_apply]
        rcases s i with a | a <;> simp [Formalism.UG.Jpq]
      · have hs : s i ≠ s j := fun h => hij (s.injective h)
        rw [Formalism.REAL.Jm, diagonal_apply_ne _ hij, submatrix_apply]
        revert hs
        rcases s i with a | a <;> rcases s j with b | b <;> simp +contextual [Formalism.UG.Jpq, Matrix.one_apply]
    refine ⟨fun i => (s i).isLeft, A.submatrix s id, ?_, ?_⟩
    · refine IsUnit.of_mul_eq_one (B.submatrix id s) ?_
      rw [← submatrix_mul A B s id s Function.bijective_id, hAB, submatrix_one_equiv]
    · rw [hJ, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hA]
      rfl
  choose ε fr h using key
  exact ⟨ε, fr, h⟩

theorem const_mem_forms (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (a : ℂ) :
    (fun _ => a) ∈ forms θ V U ε fr (fun τ => Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ) (fun _ _ => 0) := by
  refine ⟨isAutFunSm_const θ V a, fun _ _ _ _ => rfl, fun τ x => Submodule.subset_span ⟨LinearMap.id, a, rfl⟩,
    fun τ k => ?_⟩
  rw [zero_smul, gelf]
  refine Finset.sum_eq_zero fun idx _ => ?_
  rw [List.ofFn_succ, List.foldr_cons]
  obtain ⟨b, hb⟩ := foldr_const V (List.ofFn fun i : Fin k =>
    RderC θ V τ (Matrix.single (idx i.succ) (idx (i.succ + 1)) 1)) (fun f hf c₀ => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      exact ⟨0, RderC_const θ V τ _ c₀⟩) a
  rw [hb, RderC_const]
  rfl

theorem isContRep_trivial {K : Type} [Group K] [TopologicalSpace K] : IsContRep (Representation.trivial ℂ K ℂ) :=
  fun ℓ w => (continuous_const : Continuous fun _ : K => ℓ w)

end AutFin

end GlobalTheory.Published

end
