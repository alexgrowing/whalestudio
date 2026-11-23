import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
import Formalism.LocalToGlobal.GlobalTheory.GL6.CoordMapInjective
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondCommDistinctPlaces
import Formalism.LocalToGlobal.GlobalTheory.GL6.AdmissibleOfSplitAndRoundTrips

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Classical

variable {D : D7} {u : D.what₂.Word}

def levelZeroValues (Tf : FormsTied D u) : Submodule ℂ ((D.mem u).C.Y 0 → ℂ) :=
  (ValC (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) ((D.fm u).lam 0)).comap
    (LinearMap.funLeft ℂ ℂ (Tf.val 0 (Nat.zero_le _)).eY.symm)

theorem rational_stabiliser_trivial (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (c : (D.mem u).C.cls 0)
    (γ : GL (Fin (D.R.N 0)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hm : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∈
      (Tf.cls 0 (Nat.zero_le _)).lev.U.map (MulAut.conj ((Tf.cls 0 (Nat.zero_le _)).y c).1).toMonoidHom) :
    γ = 1 := by
  have hr := ((Tf.cls 0 (Nat.zero_le _)).stabI_range c ⟨γ, hγ⟩).2 hm
  obtain ⟨s, hs⟩ := hr
  haveI := hS c
  rw [Subsingleton.elim s 1, map_one] at hs
  exact (congrArg Subtype.val hs).symm

theorem mem_forms_level_zero_iff (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u)
    (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :
    φ ∈ (D.mem u).A.Mu0 ↔ ∀ c, φ c ∈ levelZeroValues Tf := by
  rw [Mu0_iff (Tf.val 0 (Nat.zero_le _)) φ]
  constructor
  · intro h c
    obtain ⟨g, hg, hgφ⟩ := Submodule.mem_map.1 h
    have hv := Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2 ((Tf.cls 0 (Nat.zero_le _)).y c) (Set.mem_univ _)
    have e : g ((Tf.cls 0 (Nat.zero_le _)).y c) = fun z => φ c ((Tf.val 0 (Nat.zero_le _)).eY.symm z) :=
      congrFun hgφ c
    show (fun z => φ c ((Tf.val 0 (Nat.zero_le _)).eY.symm z)) ∈
      ValC (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) ((D.fm u).lam 0)
    rw [← e]
    exact hv
  · intro h
    exact adelic_function_ext (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (embedding_conj_compat D) ((D.fm u).lam 0)
      (Tf.cls 0 (Nat.zero_le _)).y (Tf.cls 0 (Nat.zero_le _)).y_bij (rational_stabiliser_trivial Tf hS) _ (fun c => h c)

theorem forms_level_zero_linear_equiv (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) :
    ∃ (d : ℕ) (Φ : (D.mem u).A.Mu0 ≃ₗ[ℂ] ((D.mem u).C.cls 0 → Fin d → ℂ)),
      ∀ (φ : (D.mem u).A.Mu0) c, Φ φ c = 0 ↔ (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 := by
  let Φ0 : (D.mem u).A.Mu0 ≃ₗ[ℂ] ((D.mem u).C.cls 0 → levelZeroValues Tf) :=
    { toFun := fun φ c => ⟨φ.1 c, (mem_forms_level_zero_iff Tf hS φ.1).1 φ.2 c⟩
      invFun := fun ψ => ⟨fun c => (ψ c).1, (mem_forms_level_zero_iff Tf hS _).2 fun c => (ψ c).2⟩
      map_add' := fun φ ψ => rfl
      map_smul' := fun a φ => rfl
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl }
  have hΦ0 : ∀ (φ : (D.mem u).A.Mu0) c, Φ0 φ c = 0 ↔ (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 := by
    intro φ c
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  by_cases hne : Nonempty ((D.mem u).C.cls 0)
  · obtain ⟨c0⟩ := hne
    haveI := (D.mem u).A.Mu0_fd
    have hinj : Function.Injective ((Φ0.symm : ((D.mem u).C.cls 0 → levelZeroValues Tf) →ₗ[ℂ] (D.mem u).A.Mu0) ∘ₗ
        LinearMap.single ℂ (fun _ => levelZeroValues Tf) c0) := by
      rw [LinearMap.coe_comp]
      refine Φ0.symm.injective.comp ?_
      intro a b h
      have := congrFun h c0
      simpa using this
    haveI : FiniteDimensional ℂ (levelZeroValues Tf) := FiniteDimensional.of_injective _ hinj
    refine ⟨Module.finrank ℂ (levelZeroValues Tf),
      Φ0.trans (LinearEquiv.piCongrRight fun _ => (Module.finBasis ℂ (levelZeroValues Tf)).equivFun), fun φ c => ?_⟩
    rw [← hΦ0]
    simp only [LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
    exact (Module.finBasis ℂ (levelZeroValues Tf)).equivFun.map_eq_zero_iff
  · haveI : IsEmpty ((D.mem u).C.cls 0) := not_nonempty_iff.1 hne
    haveI : Subsingleton (D.mem u).A.Mu0 := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact ⟨0, LinearEquiv.ofSubsingleton _ _, fun φ c => isEmptyElim c⟩

def t2xR (v : (D.mem u).A.vT) : ((D.mem u).A.Fv v)ˣ →* Module.End ℂ (D.mem u).A.Mu0 where
  toFun a := ((D.mem u).A.rhoT v a).restrict (fun φ hφ => (D.mem u).A.Mu0_stable v a (Submodule.mem_map_of_mem hφ))
  map_one' := by
    apply LinearMap.ext; intro φ; apply Subtype.ext
    show (D.mem u).A.rhoT v 1 φ.1 = φ.1
    rw [map_one]; rfl
  map_mul' a b := by
    apply LinearMap.ext; intro φ; apply Subtype.ext
    show (D.mem u).A.rhoT v (a * b) φ.1 = (D.mem u).A.rhoT v a ((D.mem u).A.rhoT v b φ.1)
    rw [map_mul]; rfl

def t2xU (v : (D.mem u).A.vT) [Fact (D.mem u).A.T.Prime] : ((D.mem u).A.Fv v)ˣ ≃* (ZMod (D.mem u).A.T)ˣ :=
  Units.mapEquiv (FiniteField.ringEquivOfCardEq (by rw [(D.mem u).A.card_Fv v, ZMod.card])).toMulEquiv

theorem diamond_eq_rho (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (ψ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u 0 v a ψ = (D.mem u).A.rhoT v a ψ :=
  funext fun c => ((D.fm u).rhoT_dil v a ψ c).symm

def t2xRv [Fact (D.mem u).A.T.Prime] (v : (D.mem u).A.vT) :
    (ZMod (D.mem u).A.T)ˣ →* Module.End ℂ (D.mem u).A.Mu0 :=
  (t2xR v).comp (t2xU v).symm.toMonoidHom

theorem rho_ops_commute_distinct [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2xRv (D := D) (u := u) v x) (t2xRv v' y) := by
  intro v v' hvv x y
  apply LinearMap.ext; intro φ; apply Subtype.ext
  show (D.mem u).A.rhoT v ((t2xU v).symm x) ((D.mem u).A.rhoT v' ((t2xU v').symm y) φ.1) =
    (D.mem u).A.rhoT v' ((t2xU v').symm y) ((D.mem u).A.rhoT v ((t2xU v).symm x) φ.1)
  have hφ : φ.1 ∈ (D.fm u).Fi 0 := by rw [(D.fm u).Fi_zero]; exact φ.2
  have := diamond_comm_distinct_places Tf hE 0 (Nat.zero_le _) v' v (Ne.symm hvv) ((t2xU v).symm x) ((t2xU v').symm y) φ.1 hφ
  rw [diamond_eq_rho, diamond_eq_rho, diamond_eq_rho, diamond_eq_rho] at this
  exact this

def t2xRho [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) →* Module.End ℂ (D.mem u).A.Mu0 :=
  MonoidHom.noncommPiCoprod t2xRv (rho_ops_commute_distinct Tf hE)

theorem group_rep_mulSingle_eq_rho [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT)
    (h : (ZMod (D.mem u).A.T)ˣ) (φ : (D.mem u).A.Mu0) :
    ((t2xRho Tf hE (Pi.mulSingle v h) φ : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
      (D.mem u).A.rhoT v ((t2xU v).symm h) φ.1 := by
  rw [t2xRho, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

def t2xDv [Fact (D.mem u).A.T.Prime] (v : (D.mem u).A.vT) :
    (ZMod (D.mem u).A.T)ˣ →* Function.End ((D.mem u).C.cls 0) where
  toFun h := (D.fm u).dil 0 v ((t2xU v).symm h)
  map_one' := by
    funext c
    show (D.fm u).dil 0 v ((t2xU v).symm 1) c = c
    rw [map_one, (D.fm u).dil_one]
  map_mul' a b := by
    funext c
    show (D.fm u).dil 0 v ((t2xU v).symm (a * b)) c =
      (D.fm u).dil 0 v ((t2xU v).symm a) ((D.fm u).dil 0 v ((t2xU v).symm b) c)
    rw [map_mul, (D.fm u).dil_mul]

theorem diamond_ops_commute_distinct [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2xDv (D := D) (u := u) v x) (t2xDv v' y) := by
  intro v v' hvv x y
  funext c
  obtain ⟨ka, hka, δa, ha⟩ := hE 0 (Nat.zero_le _) v ((t2xU v).symm x)
  obtain ⟨kb, hkb, δb, hb⟩ := hE 0 (Nat.zero_le _) v' ((t2xU v').symm y)
  exact dilation_commute_distinct Tf v v' hvv _ _ ka kb hka hkb δa δb ha hb c

def t2xAc [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) →* Function.End ((D.mem u).C.cls 0) :=
  MonoidHom.noncommPiCoprod t2xDv (diamond_ops_commute_distinct Tf hE)

theorem group_action_mulSingle_eq_dilation [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT)
    (h : (ZMod (D.mem u).A.T)ˣ) (c : (D.mem u).C.cls 0) :
    t2xAc Tf hE (Pi.mulSingle v h) c = (D.fm u).dil 0 v ((t2xU v).symm h) c := by
  rw [t2xAc, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem zero_of_group_action_zero [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf)
    (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) : ∀ (c : (D.mem u).C.cls 0) (φ : (D.mem u).A.Mu0),
    ((t2xRho Tf hE g φ : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 →
    (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) (t2xAc Tf hE g c) = 0 := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ => ∀ (c : (D.mem u).C.cls 0) (φ : (D.mem u).A.Mu0),
      ((t2xRho Tf hE g φ : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 →
      (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) (t2xAc Tf hE g c) = 0) ?_ ?_ ?_
  · intro a b ha hb c φ h
    rw [map_mul] at h
    have h1 := ha c (t2xRho Tf hE b φ) h
    have h2 := hb (t2xAc Tf hE a c) φ h1
    rw [mul_comm, map_mul]
    exact h2
  · intro c φ h
    rw [map_one] at h
    rw [map_one]
    exact h
  · intro v _ c φ h
    rw [group_rep_mulSingle_eq_rho, (D.fm u).rhoT_dil] at h
    rw [group_action_mulSingle_eq_dilation]
    exact ((D.fm u).dilT 0 v _ c).map_eq_zero_iff.1 h

set_option maxHeartbeats 1000000 in

theorem multi_diamond_of_group_elem [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf)
    (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) : ∃ (k : (D.mem u).A.vT → ℤ)
      (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      MultiPlaceDiamond (Tf.cls 0 (Nat.zero_le _)).lev (fun v => (Tf.atT.eV v).1) (fun v => (Tf.atT.eV v).2) k δ ∧
      (∀ v, ((k v : ℤ) : (D.mem u).A.Fv v) = (((t2xU v).symm (g v) : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v)) ∧
      ∀ c, (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y (t2xAc Tf hE g c)) : Cls (Tf.cls 0 (Nat.zero_le _)).lev) =
        Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c * δ) := by
  have hplinj : Function.Injective (fun v : (D.mem u).A.vT => (Tf.atT.eV v).1) :=
    fun a b h => Tf.atT.eV.injective (Subtype.ext h)
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ => ∃ (k : (D.mem u).A.vT → ℤ)
      (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      MultiPlaceDiamond (Tf.cls 0 (Nat.zero_le _)).lev (fun v => (Tf.atT.eV v).1) (fun v => (Tf.atT.eV v).2) k δ ∧
      (∀ v, ((k v : ℤ) : (D.mem u).A.Fv v) = (((t2xU v).symm (g v) : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v)) ∧
      ∀ c, (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y (t2xAc Tf hE g c)) : Cls (Tf.cls 0 (Nat.zero_le _)).lev) =
        Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c * δ)) ?_ ?_ ?_
  · rintro a b ⟨ka, δa, hda, hka, hca⟩ ⟨kb, δb, hdb, hkb, hcb⟩
    refine ⟨kb * ka, δb * δa, multi_diamond_mul _ _ _ hdb hda, fun v => ?_, fun c => ?_⟩
    · rw [Pi.mul_apply, Int.cast_mul, hka v, hkb v, Pi.mul_apply, map_mul, Units.val_mul, mul_comm]
    · have h1 := hca (t2xAc Tf hE b c)
      have h2 := class_mul_right_of_normalises (Tf.cls 0 (Nat.zero_le _)).lev ((Tf.cls 0 (Nat.zero_le _)).y c)
        ((Tf.cls 0 (Nat.zero_le _)).y (t2xAc Tf hE b c)) δb δa (fun κ hκ => multi_diamond_conj_mem _ _ _ hda κ hκ) (hcb c)
      have h3 : t2xAc Tf hE (a * b) c = t2xAc Tf hE a (t2xAc Tf hE b c) := by rw [map_mul]; rfl
      exact (congrArg (fun z => (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y z) : Cls (Tf.cls 0 (Nat.zero_le _)).lev)) h3).trans
        (h1.trans (h2.trans (congrArg (fun z => (Quotient.mk'' z : Cls (Tf.cls 0 (Nat.zero_le _)).lev)) (mul_assoc _ _ _))))
  · refine ⟨1, 1, multi_diamond_one _ _ _, fun v => ?_, fun c => ?_⟩
    · simp
    · rw [map_one, mul_one]
      rfl
  · intro v _
    obtain ⟨k0, hk0, δ0, hδ0⟩ := hE 0 (Nat.zero_le _) v ((t2xU v).symm (g v))
    refine ⟨Function.update 1 v k0, δ0, multi_diamond_of_is_diamond _ _ _ hplinj v hδ0, fun v' => ?_, fun c => ?_⟩
    · by_cases hv : v' = v
      · subst hv
        rw [Function.update_self, hk0, Pi.mulSingle_eq_same]
      · rw [Function.update_of_ne hv, Pi.mulSingle_eq_of_ne hv, map_one, Pi.one_apply, Int.cast_one, Units.val_one]
    · rw [group_action_mulSingle_eq_dilation]
      exact (Tf.val 0 (Nat.zero_le _)).dil v _ k0 hk0 c δ0 hδ0

theorem group_acts_freely_classes [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf)
    (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) (c : (D.mem u).C.cls 0) (hgc : t2xAc Tf hE g c = c) : g = 1 := by
  obtain ⟨k, δ, hδ, hk, hcl⟩ := multi_diamond_of_group_elem Tf hE g
  have hfix : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c * δ) : Cls (Tf.cls 0 (Nat.zero_le _)).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c) := by
    rw [← hcl c, hgc]
  have h1 := diamond_free_on_classes Tf hS k (fun v => by rw [hk v]; exact Units.ne_zero _) δ hδ c hfix
  funext v
  have h2 := h1 v
  rw [hk v] at h2
  have h3 : (t2xU v).symm (g v) = 1 := Units.ext h2
  rw [Pi.one_apply]
  exact (MulEquiv.map_eq_one_iff _).1 h3

section ModelOf

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}

theorem free_rank_model_of_free_action (A : ColumnsAtT R C) {H : Type} [CommGroup H] [Fintype H] (e : ∀ v, (A.Fv v)ˣ ≃* H) {d : ℕ}
    (Φ : A.Mu0 ≃ₗ[ℂ] (C.cls 0 → Fin d → ℂ)) (ρ : (A.vT → H) →* Module.End ℂ A.Mu0)
    [MulAction (A.vT → H) (C.cls 0)]
    (hmono : ∀ (g : A.vT → H) (c : C.cls 0) (φ : A.Mu0), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : A.vT → H) (c : C.cls 0), g • c = c → g = 1)
    (hρ : ∀ v a (φ : A.Mu0), ((ρ (Pi.mulSingle v (e v a)) φ : A.Mu0) : C.cls 0 → C.Y 0 → ℂ) = A.rhoT v a φ.1) :
    Nonempty (FreeRankModel A) := by
  letI := productMulActionFirstFactor (A.vT → H) (MulAction.orbitRel.Quotient (A.vT → H) (C.cls 0) × Fin d)
  refine ⟨⟨H, (A.vT → H) × (MulAction.orbitRel.Quotient (A.vT → H) (C.cls 0) × Fin d), e,
    orbitDecompositionLinearEquiv Φ ρ hmono hfree, ?_, ?_⟩⟩
  · intro g x h
    have h1 : g * x.1 = x.1 := congrArg Prod.fst h
    exact mul_eq_right.1 h1
  · intro v a φ h x
    have h1 : (⟨A.rhoT v a (φ : C.cls 0 → C.Y 0 → ℂ), h⟩ : A.Mu0) = ρ (Pi.mulSingle v (e v a)) φ :=
      Subtype.ext (hρ v a φ).symm
    rw [t2xEquiv_apply, t2xEquiv_apply, h1, coordMap_intertwines]
    rfl

end ModelOf

theorem free_rank_model_of_diamonds (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf) :
    Nonempty (FreeRankModel (D.mem u).A) := by
  haveI : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  obtain ⟨d, Φ, hΦ⟩ := forms_level_zero_linear_equiv Tf hS
  letI : MulAction ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) ((D.mem u).C.cls 0) := MulAction.ofEndHom (t2xAc Tf hE)
  refine free_rank_model_of_free_action (D.mem u).A (fun v => t2xU v) Φ (t2xRho Tf hE) ?_ ?_ ?_
  · intro g c φ h
    rw [hΦ] at h ⊢
    exact zero_of_group_action_zero Tf hE g c φ h
  · exact fun g c h => group_acts_freely_classes Tf hS hE g c h
  · intro v a φ
    rw [group_rep_mulSingle_eq_rho, MulEquiv.symm_apply_apply]

theorem free_rank_model_of_split (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hs : SplitAtT Tf.atT) :
    Nonempty (FreeRankModel (D.mem u).A) :=
  free_rank_model_of_diamonds Tf hS (diamond_elements_of_split Tf hs)

theorem level_zero_values_ne_bot (Tf : FormsTied D u) : ∃ w ∈ levelZeroValues Tf, w ≠ 0 := by
  have hemb : Formalism.L2.Col.embAt (RingHom.id ℂ) (embT D) = embT D := funext fun τ => RingHom.id_comp _
  let o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (Formalism.L2.Col.embAt (RingHom.id ℂ) (embT D))) :=
    ⟨fun _ => 1, fun τ => by simp⟩
  have h1 := Formalism.L2.Col.evV_mem_ValC (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ)
    (Formalism.L2.Col.extV ℂ ((D.fm u).lam 0))
  have h2 := Formalism.L2.Col.evV_extV_ne_zero (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ) o
  rw [hemb] at h1 h2
  set F := Formalism.L2.Col.evV (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ)
    (Formalism.L2.Col.extV ℂ ((D.fm u).lam 0)) with hF
  refine ⟨fun z => F ((Tf.val 0 (Nat.zero_le _)).eY z), ?_, ?_⟩
  · show (fun y => F ((Tf.val 0 (Nat.zero_le _)).eY ((Tf.val 0 (Nat.zero_le _)).eY.symm y))) ∈
      ValC (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) ((D.fm u).lam 0)
    simp only [Equiv.apply_symm_apply]
    exact h1
  · intro h
    apply h2
    funext y
    have := congrFun h ((Tf.val 0 (Nat.zero_le _)).eY.symm y)
    simp only [Equiv.apply_symm_apply] at this
    exact this

theorem rank_level_zero_pos (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : 0 < D.duS u := by
  obtain ⟨c0, -⟩ := (Tf.cls 0 (Nat.zero_le _)).y_bij.2 (Quotient.mk'' 1)
  obtain ⟨w, hw, hw0⟩ := level_zero_values_ne_bot Tf
  have hmem : (Pi.single c0 w : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) ∈ (D.mem u).A.Mu0 := by
    rw [mem_forms_level_zero_iff Tf hS]
    intro c
    by_cases hc : c = c0
    · subst hc; rw [Pi.single_eq_same]; exact hw
    · rw [Pi.single_eq_of_ne hc]; exact (levelZeroValues Tf).zero_mem
  haveI := (D.mem u).A.Mu0_fd
  unfold Formalism.BasicNotions.D7.duS
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨_, hmem⟩, fun h => hw0 ?_⟩
  have := congrFun (congrArg Subtype.val h) c0
  simpa using this

theorem ramified_lattice_of_slope_and_length (hs : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → SplitAtT Tf.atT)
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u → Formalism.MainNotions.product_first_zeroth_parts.admS D u →
      RamifiedSlopeFormula D u ∧ LatticeInclusionLength D u) : RamifiedLatticeFamily :=
  ramified_lattice_of_free_model fun D u hF hS hA => by
    obtain ⟨Tf, hC⟩ := hF
    exact ⟨free_rank_model_of_split Tf hA (hs D u Tf hC), rank_level_zero_pos Tf hA, h D u ⟨Tf, hC⟩ hS hA⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
