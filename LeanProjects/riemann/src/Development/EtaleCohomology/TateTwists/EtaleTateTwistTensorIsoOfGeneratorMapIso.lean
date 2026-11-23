import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTateTwistSingletonTensorGenMul

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulPf

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

theorem sec_map_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

def secL {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U :=
  (φ.hom.app (op U)).hom

def transp {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ (secL (ψ.hom.f w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (ψ.hom.f w) _) = Sec.map (ψ.hom.f w) _
    rw [sec_res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (ψ.hom.f w) _) =
      Sec.map (ψ.hom.f (w + 1)) _ + s.negOnePow • Sec.map (ψ.hom.f (w + 1)) _
    rw [sec_map_comp, ψ.hom.comm w (w + 1), ← sec_map_comp, μ.leibniz]
    simp only [Sec.map, map_add, map_zsmul_unit]

theorem transp_lift {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (U : Scheme.{0}) (w : ℤ)
    (x : Tens I J U w) : (transp μ ψ).lift U w x = Sec.map (ψ.hom.f w) (μ.lift U w x) := by
  classical
  change _ = secL (ψ.hom.f w) U (μ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, transp]

theorem transp_isTensor {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (hμ : μ.IsTensor) :
    (transp μ ψ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine loc_mono (hμ.1 U w (Sec.map (ψ.inv.f w) y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
    rw [transp_lift, hx, ← sec_res_map, sec_map_comp, ← HomologicalComplex.comp_f, ψ.inv_hom_id,
      HomologicalComplex.id_f, sec_map_id]
  · refine hμ.2 U w x ?_
    rw [transp_lift] at hx
    have := congrArg (Sec.map (ψ.inv.f w)) hx
    rw [sec_map_comp, ← HomologicalComplex.comp_f, ψ.hom_inv_id, HomologicalComplex.id_f, sec_map_id] at this
    rw [this]
    exact map_zero _

theorem sgl_map_f_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0) (Sec.map (sglι F) x) =
      Sec.map (sglι G) (Sec.map φ x) := by
  rw [sec_map_comp, sec_map_comp]
  congr 1

end LateralTheory.EtaleFoundations.TwMulPf

open LateralTheory.EtaleFoundations.TwMulPf in

def LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)), μ.IsTensor

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∃ φ : tw q k ⟶ T, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → IsIso φ

open LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_tensor_iso_of_generator_map_iso (h1 : LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists)
    (h2 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists) (h3 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso) :
    LateralTheory.EtaleFoundations.EtaleTateTwistSingletonTensorGenMul := by
  intro q _ i j k hk
  obtain ⟨T, μ, hμ⟩ := h1 q i j
  obtain ⟨φ, hφ⟩ := h2 q i j k T μ hμ hk
  have := h3 q i j k T μ hμ hk φ hφ
  let ψ : sgl T ≅ sgl (tw q k) := (CochainComplex.singleFunctor (Shv (ZMod q)) 0).mapIso (asIso φ).symm
  refine ⟨transp μ ψ, transp_isTensor μ ψ hμ, fun U ζ => ?_⟩
  change Sec.map (ψ.hom.f 0) (μ.mul U 0 0 0 (add_zero 0) _ _) = _
  rw [← hφ U ζ]
  change Sec.map (((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map (inv φ)).f 0) _ = _
  rw [sgl_map_f_zero, sec_map_comp, sec_map_comp, IsIso.hom_inv_id_assoc]
