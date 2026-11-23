import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimIdeal

variable {R : Type} [CommRing R] (I : Ideal R)

section Lin

variable (B : Type) [CommRing B] [Algebra R B]

def iota : I ⊗[R] B →ₗ[R] TrivSqZeroExt R I ⊗[R] B := (TrivSqZeroExt.inrHom R I).rTensor B

def tau : I ⊗[R] B →ₗ[R] B := TensorProduct.lid R B ∘ₗ I.subtype.rTensor B

def sig : TrivSqZeroExt R I ⊗[R] B →ₗ[R] B := tau I B ∘ₗ (TrivSqZeroExt.sndHom R I).rTensor B

theorem tau_tmul (i : I) (b : B) : tau I B (i ⊗ₜ b) = (i : R) • b := by
  simp [tau]

theorem sig_iota (y : I ⊗[R] B) : sig I B (iota I B y) = tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [sig, iota]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tau_mem (y : I ⊗[R] B) : tau I B y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b =>
    rw [tau_tmul, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i.2)
  | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy

theorem sig_mem (x : TrivSqZeroExt R I ⊗[R] B) : sig I B x ∈ I.map (algebraMap R B) := tau_mem I B _

theorem tau_mulLeft (b : B) (y : I ⊗[R] B) : tau I B ((LinearMap.mulLeft R b).lTensor I y) = b • tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i c => simp [tau_tmul, Algebra.smul_def]; ring
  | add u v hu hv => simp only [map_add, hu, hv, smul_add]

theorem exists_tau {x : B} (hx : x ∈ I.map (algebraMap R B)) : ∃ y, tau I B y = x := by
  rw [Ideal.map, Ideal.span] at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, hi, rfl⟩ := h
    exact ⟨⟨i, hi⟩ ⊗ₜ 1, by simp [tau_tmul, Algebra.smul_def]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, rfl⟩ := hx; obtain ⟨y', rfl⟩ := hx'
    exact ⟨y + y', map_add _ _ _⟩
  | smul b x _ hx =>
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(LinearMap.mulLeft R b).lTensor I y, tau_mulLeft I B b y⟩

theorem tau_injective (hB : Module.Flat R B) : Function.Injective (tau I B) :=
  (TensorProduct.lid R B).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective)

variable {B} {B' : Type} [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B')

theorem iota_nat (y : I ⊗[R] B) :
    extHom (TrivSqZeroExt R I) φ (iota I B y) = iota I B' (φ.toLinearMap.lTensor I y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [iota]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tau_nat (y : I ⊗[R] B) : tau I B' (φ.toLinearMap.lTensor I y) = φ (tau I B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [tau_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sig_nat (x : TrivSqZeroExt R I ⊗[R] B) :
    sig I B' (extHom (TrivSqZeroExt R I) φ x) = φ (sig I B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sig, tau_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Lin

end GlobalTheory.PrimIdeal

namespace GlobalTheory.PrimIdeal

theorem primI_of_ext : ∀ (R : Type) [CommRing R] (I : Ideal R), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁)
    (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) ∧
    ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R)
      (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), (∀ t, Module.Flat R (F.obj t)) → (∀ t, Module.Flat R (F'.obj t)) →
      (∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ F),
        (extMap R₁ n₀).pull2 c = (extMap R₁ n₁).pull2 c + (extMap R₁ n₂).pull2 c → c = 0) →
      PrimI I n₀ n₁ n₂ := by
  intro R _ I
  refine ⟨TrivSqZeroExt R I, inferInstance, inferInstance, TrivSqZeroExt.fstHom R R I, ?_, ?_⟩
  · intro y y' hy hy'
    have h1 : y.fst = 0 := hy
    have h2 : y'.fst = 0 := hy'
    ext
    · simp [h1, h2]
    · simp [h1, h2]
  intro D T _ _ F F' n₀ n₁ n₂ hF hF' hc z f hz hf hrel
  choose y hy using fun (t t' t'' : D) (a : t ⟶ t') (b : t' ⟶ t'') ↦ exists_tau I (F.obj t'') (hz t t' t'' a b)
  choose y' hy' using fun (t t' : T) (a : t ⟶ t') ↦ exists_tau I (F'.obj t') (hf t t' a)
  let zh : C2 (ext (TrivSqZeroExt R I) F) := fun t t' t'' a b ↦ iota I (F.obj t'') (y t t' t'' a b)
  have hzc : zh ∈ Z2 (ext (TrivSqZeroExt R I) F) := by
    intro t t' t'' t''' φ ψ χ
    have key : (mp F χ).toLinearMap.lTensor I (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ =
        y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ := by
      apply tau_injective I (F.obj t''') (hF t''')
      simp only [map_add, AlgHom.toLinearMap_apply, tau_nat, hy]
      exact z.2 φ ψ χ
    have := congrArg (iota I _) key
    simp only [map_add, ← iota_nat] at this
    exact this
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 (hc (H2.mk _ ⟨zh, hzc⟩) (by
    show H2.mk _ ((extMap _ n₀).pullbackTwoCocycle ⟨zh, hzc⟩) =
      H2.mk _ ((extMap _ n₁).pullbackTwoCocycle ⟨zh, hzc⟩) + H2.mk _ ((extMap _ n₂).pullbackTwoCocycle ⟨zh, hzc⟩)
    rw [← LinearMap.map_add (H2.mk _), H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ iota I (F'.obj t') (y' t t' a), ?_⟩
    funext t t' t'' a b
    simp only [d1_apply, Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply, CoefMap.pullCocycleTwo_apply]
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hrel t) t') t'') a) b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply] at e
    have key : (mp F' b).toLinearMap.lTensor I (y' _ _ a) - y' _ _ (a ≫ b) + y' _ _ b =
        (coefHom n₀ t'').toLinearMap.lTensor I (y _ _ _ (n₀.G.map a) (n₀.G.map b)) -
          ((coefHom n₁ t'').toLinearMap.lTensor I (y _ _ _ (n₁.G.map a) (n₁.G.map b)) +
            (coefHom n₂ t'').toLinearMap.lTensor I (y _ _ _ (n₂.G.map a) (n₂.G.map b))) := by
      apply tau_injective I (F'.obj t'') (hF' t'')
      simp only [map_add, map_sub, AlgHom.toLinearMap_apply, tau_nat, hy, hy']
      rw [e]
      rw [sub_sub]; rfl
    have := congrArg (iota I _) key
    simp only [map_add, map_sub, ← iota_nat] at this
    exact this))
  refine ⟨fun t t' a ↦ sig I (F.obj t') (g t t' a), fun t t' a ↦ sig_mem I _ _, ?_⟩
  funext t t' t'' a b
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hg t) t') t'') a) b
  simp only [d1_apply] at e ⊢
  rw [← sig_nat, ← map_sub, ← map_add]
  change sig I (F.obj t'') (mp (ext (TrivSqZeroExt R I) F) b (g t t' a) - g t t'' (a ≫ b) + g t' t'' b) = _
  rw [e]
  exact (sig_iota I _ _).trans (hy t t' t'' a b)

end GlobalTheory.PrimIdeal
