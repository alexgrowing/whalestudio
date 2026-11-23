import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CrLocal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem qcont_map {X V W : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W]
    [Module ℚ_[l] W] (f : V →ₗ[ℚ_[l]] W) {c : X → V} (hc : QCont l c) : QCont l fun x => f (c x) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : ContinuousAdd W := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap f).comp hc

theorem qcont_add {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c d : X → V}
    (hc : QCont l c) (hd : QCont l d) : QCont l fun x => c x + d x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hc hd

theorem qcont_sum {X V ι : Type} [Fintype ι] [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c : ι → X → V}
    (hc : ∀ i, QCont l (c i)) : QCont l fun x => ∑ i, c i x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact continuous_finset_sum _ fun i _ => hc i

theorem contAction_of_qcont {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V)
    (h : ∀ v, QCont l fun g => ρ g v) : ContAction ρ := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  have h' : ∀ v, Continuous fun g => ρ g v := fun v => by
    have := h v
    unfold QCont at this
    rwa [← eq_moduleTopology ℚ_[l] V] at this
  let b := Module.finBasis ℚ_[l] V
  have e : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.coord i p.2 • ρ p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2, map_sum]
    simp only [map_smul, Basis.coord_apply]
  unfold ReciprocityTheory.Gal.ContAction
  rw [e]
  exact continuous_finset_sum _ fun i _ =>
    ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp continuous_snd).smul ((h' _).comp continuous_fst)

theorem qcont_colRep {B : Type} [CommRing B] [Algebra ℚ_[l] B] (ρ : G →* GL (Fin 3) B)
    (h : ∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) (v : Fin 3 → B) :
    QCont l fun g => resCoef ℚ_[l] (colRep ρ) g v := by
  have e : (fun g => resCoef ℚ_[l] (colRep ρ) g v) = fun g => ∑ i, ∑ j,
      ((LinearMap.single ℚ_[l] (fun _ : Fin 3 => B) i).comp (LinearMap.mulRight ℚ_[l] (v j)))
        ((ρ g : Matrix (Fin 3) (Fin 3) B) i j) := by
    funext g
    ext k
    change (ρ g : Matrix (Fin 3) (Fin 3) B).mulVec v k = _
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact qcont_sum fun i => qcont_sum fun j => qcont_map _ (h i j)

variable [IsTopologicalGroup G] {φ : G →* GQ l}

theorem cr_sub (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (f : V →ₗ[ℚ_[l]] W) (hf : ∀ g x, f (ρ g x) = σ g (f x)) (hi : Function.Injective f) (h : IsCr φ σ) :
    IsCr φ ρ := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact ((isCrys_isDR_sub_quot φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ) f hf).1 hi).1 h

theorem cr_prod (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (h : IsCr φ ρ) (h' : IsCr φ σ) : IsCr φ (ρ.prod σ) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact (isCrys_isDR_prod φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ)).1 h h'

theorem exists_cr_of_finset (hφ : IsOpenEmbedding φ) {V ι : Type} [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (N : ι → Set V)
    (h : ∀ i, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → x ∈ N i) (S : Finset ι) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → ∀ i ∈ S, x ∈ N i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, 0, fun v => ?_, ?_,
      fun _ _ => Subsingleton.elim _ _, by simp⟩
    · exact @continuous_const _ _ _ (moduleTopology ℚ_[l] PUnit) v
    · unfold IsCr
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, mul_zero]
  | insert a S _ ih =>
    obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := ih
    obtain ⟨W', _, _, _, σ', f', h1', h2', h3', h4'⟩ := h a
    refine ⟨W × W', inferInstance, inferInstance, inferInstance, σ.prod σ', f.prod f', fun v => ?_,
      cr_prod hφ σ σ' h1 h1' h2 h2', fun g x => ?_, fun x hx i hi => ?_⟩
    · have := qcont_add (qcont_map (LinearMap.inl ℚ_[l] W W') (h1 v.1)) (qcont_map (LinearMap.inr ℚ_[l] W W') (h1' v.2))
      convert this using 2 with g
      ext <;> simp [Representation.prod]
    · ext <;> simp [Representation.prod, h3, h3']
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h4' x (congrArg Prod.snd hx)
      · exact h4 x (congrArg Prod.fst hx) i hi

theorem isCr_of_local : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (ρ : G →* GL (Fin 3) B), (∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) → (∀ (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra B B'] [IsScalarTower ℚ_[l] B B'], IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (algebraMap B B')).comp ρ))) → IsCr φ (colRep ρ) := by
  intro l _ G _ _ _ φ hφ B _ _ _ ρ hc h
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := exists_cr_of_finset hφ (resCoef ℚ_[l] (colRep ρ))
    (fun m : MaximalSpectrum B => {v | ∀ i, algebraMap B (Localization.AtPrime m.asIdeal) (v i) = 0})
    (fun m => by
      let a : B →ₗ[ℚ_[l]] Localization.AtPrime m.asIdeal :=
        (IsScalarTower.toAlgHom ℚ_[l] B (Localization.AtPrime m.asIdeal)).toLinearMap
      haveI : Module.Finite ℚ_[l] (Localization.AtPrime m.asIdeal) :=
        Module.Finite.of_surjective a (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
      refine ⟨Fin 3 → Localization.AtPrime m.asIdeal, inferInstance, inferInstance, inferInstance,
        resCoef ℚ_[l] (colRep ((Matrix.GeneralLinearGroup.map
          (algebraMap B (Localization.AtPrime m.asIdeal))).comp ρ)), a.compLeft (Fin 3),
        qcont_colRep _ fun i j => qcont_map a (hc i j), h _, fun g x => ?_, fun x hx i => congrFun hx i⟩
      ext k
      exact RingHom.map_mulVec (algebraMap B (Localization.AtPrime m.asIdeal)) _ x k) Finset.univ
  refine cr_sub hφ (resCoef ℚ_[l] (colRep ρ)) σ (qcont_colRep ρ hc) h1 f h3 ?_ h2
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  exact eq_zero_of_localization _ fun J hJ => h4 x hx ⟨J, hJ⟩ (Finset.mem_univ _) i

end GlobalTheory.CrLocal
