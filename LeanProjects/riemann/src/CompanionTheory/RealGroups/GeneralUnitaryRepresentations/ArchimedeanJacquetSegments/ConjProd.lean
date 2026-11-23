import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace CompanionTheory.RgGu.NR.ConjProd

def Cj (Y : Type) : Type := Y

instance (Y : Type) [AddCommGroup Y] : AddCommGroup (Cj Y) := inferInstanceAs (AddCommGroup Y)

instance (Y : Type) [AddCommGroup Y] [Module ℂ Y] : Module ℂ (Cj Y) := Module.compHom Y (starRingEnd ℂ)

def semiInv {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) : Y →ₛₗ[starRingEnd ℂ] X where
  toFun := Function.surjInv hφ.2
  map_add' a b := hφ.1 (by rw [map_add, Function.surjInv_eq hφ.2, Function.surjInv_eq hφ.2,
    Function.surjInv_eq hφ.2])
  map_smul' c y := hφ.1 (by
    rw [Function.surjInv_eq hφ.2, map_smulₛₗ, Function.surjInv_eq hφ.2]
    simp)

theorem semiInv_apply {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (y : Y) : φ (semiInv φ hφ y) = y :=
  Function.surjInv_eq hφ.2 y

theorem semiInv_apply' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (x : X) : semiInv φ hφ (φ x) = x :=
  hφ.1 (semiInv_apply φ hφ (φ x))

section Tensor

variable {α : Type} [Fintype α] {X Y : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

omit [Fintype α] in
theorem update_comp (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) [DecidableEq α] (x : ∀ a, X a) (i : α) (w : X i) :
    (fun a => φ a (Function.update x i w a)) = Function.update (fun a => φ a (x a)) i (φ i w) := by
  funext a
  exact Function.apply_update (fun a => φ a) x i w a

def mlin (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) : MultilinearMap ℂ X (Cj (⨂[ℂ] a, Y a)) where
  toFun x := (PiTensorProduct.tprod ℂ (fun a => φ a (x a)) : ⨂[ℂ] a, Y a)
  map_update_add' x i u v := by
    show (PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i (u + v) a)) : ⨂[ℂ] a, Y a) =
      PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i u a)) +
        PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i v a))
    rw [update_comp, update_comp, update_comp, map_add, MultilinearMap.map_update_add]
  map_update_smul' x i c u := by
    show (PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i (c • u) a)) : ⨂[ℂ] a, Y a) =
      starRingEnd ℂ c • PiTensorProduct.tprod ℂ (fun a => φ a (Function.update x i u a))
    rw [update_comp, update_comp, map_smulₛₗ, MultilinearMap.map_update_smul]

def tmap (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) : (⨂[ℂ] a, X a) →ₛₗ[starRingEnd ℂ] (⨂[ℂ] a, Y a) where
  toFun t := (PiTensorProduct.lift (mlin φ) t : Cj (⨂[ℂ] a, Y a))
  map_add' s t := by
    show (PiTensorProduct.lift (mlin φ) (s + t) : Cj (⨂[ℂ] a, Y a)) = _
    rw [map_add]
    rfl
  map_smul' c t := by
    show (PiTensorProduct.lift (mlin φ) (c • t) : Cj (⨂[ℂ] a, Y a)) = _
    rw [map_smul]
    rfl

theorem tmap_tprod (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) (x : ∀ a, X a) :
    tmap φ (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (fun a => φ a (x a)) := by
  show (PiTensorProduct.lift (mlin φ) (PiTensorProduct.tprod ℂ x) : Cj (⨂[ℂ] a, Y a)) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem tmap_comp (φ : ∀ a, X a →ₛₗ[starRingEnd ℂ] Y a) (ψ : ∀ a, Y a →ₛₗ[starRingEnd ℂ] X a)
    (h : ∀ a (x : X a), ψ a (φ a x) = x) (t : ⨂[ℂ] a, X a) : tmap ψ (tmap φ t) = t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smulₛₗ, map_smulₛₗ, tmap_tprod, tmap_tprod]
    simp [h]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

end Tensor

theorem conjEquiv_piTensor {α : Type} [Fintype α] {Γ X Y : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (Γ a) (X a)) (σ : ∀ a, Representation ℂ (Γ a) (Y a))
    (h : ∀ a, ConjEquiv (π a) (σ a)) : ConjEquiv (piTensor π) (piTensor σ) := by
  choose φ hφ heq using h
  refine ⟨tmap φ, ⟨fun s t hst => ?_, fun t => ⟨tmap (fun a => semiInv (φ a) (hφ a)) t, ?_⟩⟩, fun g t => ?_⟩
  · have := congrArg (tmap (fun a => semiInv (φ a) (hφ a))) hst
    rwa [tmap_comp _ _ (fun a x => semiInv_apply' (φ a) (hφ a) x),
      tmap_comp _ _ (fun a x => semiInv_apply' (φ a) (hφ a) x)] at this
  · exact tmap_comp (fun a => semiInv (φ a) (hφ a)) φ (fun a y => semiInv_apply (φ a) (hφ a) y) t
  · induction t using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul, piTensor_tprod, tmap_tprod, tmap_tprod, piTensor_tprod]
      congr 2
      funext a
      exact heq a (g a) (x a)
    | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

section Ind

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  {n : Type} [Fintype n] [DecidableEq n]

theorem star_deltaHalf (g : Levi k m) : starRingEnd ℂ (deltaHalf k m g : ℂ) = deltaHalf k m g := by
  rw [deltaHalf_apply, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  have e : ((modExp m a : ℂ) / 2) = (((modExp m a : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  show starRingEnd ℂ (((nabs k (Matrix.GeneralLinearGroup.det (g a)) : ℝ) : ℂ) ^ ((modExp m a : ℂ) / 2)) =
    ((nabs k (Matrix.GeneralLinearGroup.det (g a)) : ℝ) : ℂ) ^ ((modExp m a : ℂ) / 2)
  rw [e, ← Complex.ofReal_cpow (nabs_pos' k _).le, Complex.conj_ofReal]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def indMap (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {τ : Representation ℂ (Levi k m) W}
    (φ : V →ₛₗ[starRingEnd ℂ] W) (hφ : ∀ g v, φ (ρ g v) = τ g (φ v)) :
    IndSp e ρ →ₛₗ[starRingEnd ℂ] IndSp e τ where
  toFun f := ⟨⟨fun g => φ (f.1.1 g), fun p g => by
      show φ (f.1.1 (p * g)) = (deltaHalf k m (leviProj k e p) : ℂ) • τ (leviProj k e p) (φ (f.1.1 g))
      rw [parInd_law e ρ f p g, map_smulₛₗ, star_deltaHalf, hφ]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
      have hg' : ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) g f.1 = f.1 := hg
      apply Subtype.ext
      funext x
      exact congrArg φ (congrFun (congrArg Subtype.val hg') x))⟩
  map_add' f f' := by
    apply Subtype.ext; apply Subtype.ext; funext g
    exact map_add φ (f.1.1 g) (f'.1.1 g)
  map_smul' c f := by
    apply Subtype.ext; apply Subtype.ext; funext g
    exact map_smulₛₗ φ c (f.1.1 g)

theorem indMap_apply (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {τ : Representation ℂ (Levi k m) W}
    (φ : V →ₛₗ[starRingEnd ℂ] W) (hφ : ∀ g v, φ (ρ g v) = τ g (φ v)) (f : IndSp e ρ) (g : GL n k) :
    (indMap e φ hφ f).1.1 g = φ (f.1.1 g) := rfl

theorem conjEquiv_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) V)
    (τ : Representation ℂ (Levi k m) W) (h : ConjEquiv ρ τ) : ConjEquiv (parInd e ρ) (parInd e τ) := by
  obtain ⟨φ, hφ, heq⟩ := h
  have hinv : ∀ g w, semiInv φ hφ (τ g w) = ρ g (semiInv φ hφ w) := fun g w => by
    apply hφ.1
    rw [semiInv_apply, heq, semiInv_apply]
  refine ⟨indMap e φ heq, ⟨fun f f' hff => ?_, fun f => ⟨indMap e (semiInv φ hφ) hinv f, ?_⟩⟩, fun g f => ?_⟩
  · apply Subtype.ext; apply Subtype.ext; funext x
    apply hφ.1
    have := congrArg (fun F : IndSp e τ => F.1.1 x) hff
    simpa only [indMap_apply] using this
  · apply Subtype.ext; apply Subtype.ext; funext x
    show φ (semiInv φ hφ (f.1.1 x)) = f.1.1 x
    exact semiInv_apply φ hφ _
  · apply Subtype.ext; apply Subtype.ext; funext x
    rfl

end Ind

end CompanionTheory.RgGu.NR.ConjProd

namespace CompanionTheory.RgGu.NR

open ConjProd in
theorem conjProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjProd k := by
  intro h N d hd X Y _ _ _ _ π σ hc
  exact conjEquiv_parInd _ _ _ (conjEquiv_piTensor π σ hc)

end CompanionTheory.RgGu.NR

end
