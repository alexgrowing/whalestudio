import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.EqOneOfCoprimeTorsionTwoPrimes
import Formalism.LocalToGlobal.GlobalTheory.GL6.CoordMapInjective
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.DiamondCommDistinctPlaces
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.LocalDiamondOfSplitIdempotent

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Classical

variable {D : D7} {u : D.what₂.Word}

def levelZeroValues (Tf : Forms0 D u) : Submodule ℂ ((D.mem u).C.Y 0 → ℂ) :=
  (ValC (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) ((D.fm u).lam 0)).comap
    (LinearMap.funLeft ℂ ℂ (Tf.val 0 (Nat.zero_le _) rfl).eY.symm)

theorem rational_stabiliser_trivial (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (c : (D.mem u).C.cls 0)
    (γ : GL (Fin (D.R.N 0)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hm : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ ∈
      (Tf.cls 0 (Nat.zero_le _) rfl).lev.U.map (MulAut.conj ((Tf.cls 0 (Nat.zero_le _) rfl).y c).1).toMonoidHom) :
    γ = 1 := by
  obtain ⟨s, hs⟩ := ((Tf.cls 0 (Nat.zero_le _) rfl).stabI_range c ⟨γ, hγ⟩).2 hm
  haveI : Subsingleton ((D.mem u).C.stab 0 c) := hS c
  rw [Subsingleton.elim s 1, map_one] at hs
  simpa using (congrArg Subtype.val hs).symm

theorem mem_forms_level_zero_iff (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u)
    (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :
    φ ∈ (D.mem u).A.Mu0 ↔ ∀ c, φ c ∈ levelZeroValues Tf := by
  rw [Formalism.L2.Forms.Mu0_iff (Tf.val 0 (Nat.zero_le _) rfl)]
  constructor
  · rintro ⟨g, hg, hgφ⟩ c
    have hv := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((Tf.cls 0 (Nat.zero_le _) rfl).y c)
      (Set.mem_univ _)
    have hc : g ((Tf.cls 0 (Nat.zero_le _) rfl).y c) =
        fun z => φ c ((Tf.val 0 (Nat.zero_le _) rfl).eY.symm z) := congrFun hgφ c
    have h2 : (fun z => φ c ((Tf.val 0 (Nat.zero_le _) rfl).eY.symm z)) ∈
        ValC (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) ((D.fm u).lam 0) := hc ▸ hv
    exact h2
  · intro h
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.adelic_function_ext (Tf.cls 0 (Nat.zero_le _) rfl).lev (embT D)
      (fun τ x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.embedding_conj_compat D τ x) ((D.fm u).lam 0)
      (Tf.cls 0 (Nat.zero_le _) rfl).y (Tf.cls 0 (Nat.zero_le _) rfl).y_bij
      (fun c γ hγ hm => rational_stabiliser_trivial Tf hS c γ hγ hm) _ (fun c => h c)

theorem forms_level_zero_linear_equiv (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) :
    ∃ (d : ℕ) (Φ : (D.mem u).A.Mu0 ≃ₗ[ℂ] ((D.mem u).C.cls 0 → Fin d → ℂ)),
      ∀ (φ : (D.mem u).A.Mu0) c, Φ φ c = 0 ↔ (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 := by
  classical
  let e1 : (D.mem u).A.Mu0 ≃ₗ[ℂ] ((D.mem u).C.cls 0 → levelZeroValues Tf) :=
    { toFun := fun φ c => ⟨(φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c, (mem_forms_level_zero_iff Tf hS φ).1 φ.2 c⟩
      invFun := fun ψ => ⟨fun c => (ψ c : (D.mem u).C.Y 0 → ℂ), (mem_forms_level_zero_iff Tf hS _).2 fun c => (ψ c).2⟩
      map_add' := fun φ ψ => by funext c; rfl
      map_smul' := fun r φ => by funext c; rfl
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl }
  have he1 : ∀ (φ : (D.mem u).A.Mu0) c,
      e1 φ c = 0 ↔ (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 := by
    intro φ c
    show (⟨(φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c, _⟩ : levelZeroValues Tf) = 0 ↔ _
    rw [Subtype.ext_iff]
    rfl
  by_cases hne : Nonempty ((D.mem u).C.cls 0)
  · obtain ⟨c0⟩ := hne
    haveI : FiniteDimensional ℂ (D.mem u).A.Mu0 := (D.mem u).A.Mu0_fd
    haveI : Module.Finite ℂ (levelZeroValues Tf) :=
      Module.Finite.of_surjective
        ((LinearMap.proj (R := ℂ) (φ := fun _ : (D.mem u).C.cls 0 => levelZeroValues Tf) c0).comp e1.toLinearMap)
        (fun w => ⟨e1.symm (fun _ => w), by simp⟩)
    let b := Module.finBasis ℂ (levelZeroValues Tf)
    refine ⟨Module.finrank ℂ (levelZeroValues Tf), e1.trans (LinearEquiv.piCongrRight fun _ => b.equivFun), ?_⟩
    intro φ c
    simp only [LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
    rw [LinearEquiv.map_eq_zero_iff]
    exact he1 φ c
  · haveI : IsEmpty ((D.mem u).C.cls 0) := not_nonempty_iff.mp hne
    haveI : Subsingleton (D.mem u).A.Mu0 :=
      ⟨fun φ ψ => Subtype.ext (Subsingleton.elim _ _)⟩
    refine ⟨0, LinearEquiv.ofSubsingleton _ _, ?_⟩
    intro φ c
    exact isEmptyElim c

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
    Formalism.MainNotions.product_first_zeroth_parts.dia D u 0 v a ψ = (D.mem u).A.rhoT v a ψ := by
  rw [Formalism.MainNotions.product_first_zeroth_parts.dia_zero]

def t2xRv [Fact (D.mem u).A.T.Prime] (v : (D.mem u).A.vT) :
    (ZMod (D.mem u).A.T)ˣ →* Module.End ℂ (D.mem u).A.Mu0 :=
  (t2xR v).comp (t2xU v).symm.toMonoidHom

theorem rho_ops_commute_distinct [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2xRv (D := D) (u := u) v x) (t2xRv v' y) := by
  intro v v' hvv x y
  unfold Commute SemiconjBy
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  show (D.mem u).A.rhoT v ((t2xU v).symm x) ((D.mem u).A.rhoT v' ((t2xU v').symm y) φ.1) =
    (D.mem u).A.rhoT v' ((t2xU v').symm y) ((D.mem u).A.rhoT v ((t2xU v).symm x) φ.1)
  simp only [← diamond_eq_rho]
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.diamond_comm_distinct_places Tf hE 0 (Nat.zero_le _) rfl v' v (Ne.symm hvv) _ _ φ.1 (by rw [(D.fm u).Fi_zero]; exact φ.2)

def t2xRho [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) :
    ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) →* Module.End ℂ (D.mem u).A.Mu0 :=
  MonoidHom.noncommPiCoprod t2xRv (rho_ops_commute_distinct Tf hE)

theorem group_rep_mulSingle_eq_rho [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT)
    (h : (ZMod (D.mem u).A.T)ˣ) (φ : (D.mem u).A.Mu0) :
    ((t2xRho Tf hE (Pi.mulSingle v h) φ : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
      (D.mem u).A.rhoT v ((t2xU v).symm h) φ.1 := by
  simp only [t2xRho, MonoidHom.noncommPiCoprod_mulSingle]
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

theorem diamond_ops_commute_distinct [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2xDv (D := D) (u := u) v x) (t2xDv v' y) := by
  intro v v' hvv x y
  obtain ⟨ka, hka, δa, ha⟩ := hE 0 (Nat.zero_le _) rfl v ((t2xU v).symm x)
  obtain ⟨kb, hkb, δb, hb⟩ := hE 0 (Nat.zero_le _) rfl v' ((t2xU v').symm y)
  unfold Commute SemiconjBy
  funext c
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.dilation_commute_distinct Tf v v' hvv _ _ ka kb hka hkb δa δb ha hb c

def t2xAc [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) :
    ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) →* Function.End ((D.mem u).C.cls 0) :=
  MonoidHom.noncommPiCoprod t2xDv (diamond_ops_commute_distinct Tf hE)

theorem group_action_mulSingle_eq_dilation [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT)
    (h : (ZMod (D.mem u).A.T)ˣ) (c : (D.mem u).C.cls 0) :
    t2xAc Tf hE (Pi.mulSingle v h) c = (D.fm u).dil 0 v ((t2xU v).symm h) c := by
  simp only [t2xAc, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem zero_of_group_action_zero [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf)
    (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) : ∀ (c : (D.mem u).C.cls 0) (φ : (D.mem u).A.Mu0),
    ((t2xRho Tf hE g φ : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 →
    (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) (t2xAc Tf hE g c) = 0 := by
  rw [← Finset.univ_prod_mulSingle g]
  apply Finset.prod_induction _ (fun g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ =>
    ∀ (c : (D.mem u).C.cls 0) (φ : (D.mem u).A.Mu0),
      ((t2xRho Tf hE g φ : (D.mem u).A.Mu0) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) c = 0 →
      (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) (t2xAc Tf hE g c) = 0)
  · intro a b ha hb c φ hab
    rw [map_mul, Module.End.mul_apply] at hab
    have h2 := hb _ φ (ha c _ hab)
    rw [mul_comm a b, map_mul]
    exact h2
  · intro c φ h1
    rw [map_one] at h1 ⊢
    exact h1
  · intro v _ c φ hv
    rw [group_rep_mulSingle_eq_rho, (D.fm u).rhoT_dil] at hv
    rw [group_action_mulSingle_eq_dilation]
    exact (LinearEquiv.map_eq_zero_iff _).1 hv

set_option maxHeartbeats 1000000 in

theorem multi_diamond_of_group_elem [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hE : DiamondElementsExist Tf)
    (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) : ∃ (k : (D.mem u).A.vT → ℤ)
      (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      MultiPlaceDiamond (Tf.cls 0 (Nat.zero_le _) rfl).lev (fun v => (Tf.atT.eV v).1) (fun v => (Tf.atT.eV v).2) k δ ∧
      (∀ v, ((k v : ℤ) : (D.mem u).A.Fv v) = (((t2xU v).symm (g v) : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v)) ∧
      ∀ c, (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y (t2xAc Tf hE g c)) : Cls (Tf.cls 0 (Nat.zero_le _) rfl).lev) =
        Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * δ) := by
  classical
  rw [← Finset.univ_prod_mulSingle g]
  apply Finset.prod_induction _ (fun g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ =>
    ∃ (k : (D.mem u).A.vT → ℤ)
      (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      MultiPlaceDiamond (Tf.cls 0 (Nat.zero_le _) rfl).lev (fun v => (Tf.atT.eV v).1) (fun v => (Tf.atT.eV v).2) k δ ∧
      (∀ v, ((k v : ℤ) : (D.mem u).A.Fv v) = (((t2xU v).symm (g v) : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v)) ∧
      ∀ c, (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y (t2xAc Tf hE g c)) : Cls (Tf.cls 0 (Nat.zero_le _) rfl).lev) =
        Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * δ))
  · rintro a b ⟨k, δ, hδ, hk, hc⟩ ⟨k', δ', hδ', hk', hc'⟩
    refine ⟨k' * k, δ' * δ, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.multi_diamond_mul _ _ _ hδ' hδ, ?_, ?_⟩
    · intro v
      simp only [Pi.mul_apply, Int.cast_mul, hk v, hk' v, map_mul, Units.val_mul]
      ring
    · intro c
      rw [map_mul]
      show (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y (t2xAc Tf hE a (t2xAc Tf hE b c))) :
        Cls (Tf.cls 0 (Nat.zero_le _) rfl).lev) = _
      rw [hc (t2xAc Tf hE b c), ← mul_assoc]
      exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.class_mul_right_of_normalises _ _ _ _ _
        (fun κ hκ => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.multi_diamond_conj_mem _ _ _ hδ κ hκ) (hc' c)
  · refine ⟨1, 1, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.multi_diamond_one _ _ _, ?_, ?_⟩
    · intro v
      simp
    · intro c
      rw [map_one, mul_one]
      rfl
  · intro v _
    obtain ⟨k0, hk0, δ, hδ⟩ := hE 0 (Nat.zero_le _) rfl v ((t2xU v).symm (g v))
    refine ⟨Function.update 1 v k0, δ, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.multi_diamond_of_is_diamond _ _ _ ?_ v hδ, ?_, ?_⟩
    · intro a b hab
      exact Tf.atT.eV.injective (Subtype.ext hab)
    · intro w
      by_cases hw : w = v
      · subst hw
        simp [hk0]
      · simp [Function.update_of_ne hw, Pi.mulSingle_eq_of_ne hw]
    · intro c
      rw [group_action_mulSingle_eq_dilation]
      exact (Tf.val 0 (Nat.zero_le _) rfl).dil v _ k0 hk0 c δ hδ

theorem group_acts_freely_classes [Fact (D.mem u).A.T.Prime] (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf)
    (g : (D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) (c : (D.mem u).C.cls 0) (hgc : t2xAc Tf hE g c = c) : g = 1 := by
  obtain ⟨k, δ, hδ, hk, hc⟩ := multi_diamond_of_group_elem Tf hE g
  have hfix := (hc c).symm
  rw [hgc] at hfix
  have hk0 : ∀ v, (k v : (D.mem u).A.Fv v) ≠ 0 := fun v => by
    rw [hk v]
    exact Units.ne_zero _
  have h1 := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.diamond_free_on_classes Tf hS k hk0 δ hδ c hfix
  funext v
  have h2 : (t2xU v).symm (g v) = 1 := Units.ext (by rw [← hk v, h1 v, Units.val_one])
  simpa using congrArg (t2xU v) h2

section ModelOf

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}

theorem free_rank_model_of_free_action (A : ColumnsAtT R C) {H : Type} [CommGroup H] [Fintype H] (e : ∀ v, (A.Fv v)ˣ ≃* H) {d : ℕ}
    (Φ : A.Mu0 ≃ₗ[ℂ] (C.cls 0 → Fin d → ℂ)) (ρ : (A.vT → H) →* Module.End ℂ A.Mu0)
    [MulAction (A.vT → H) (C.cls 0)]
    (hmono : ∀ (g : A.vT → H) (c : C.cls 0) (φ : A.Mu0), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : A.vT → H) (c : C.cls 0), g • c = c → g = 1)
    (hρ : ∀ v a (φ : A.Mu0), ((ρ (Pi.mulSingle v (e v a)) φ : A.Mu0) : C.cls 0 → C.Y 0 → ℂ) = A.rhoT v a φ.1) :
    Nonempty (FreeRankModel A) := by
  classical
  let G := A.vT → H
  let X := G × (MulAction.orbitRel.Quotient G (C.cls 0) × Fin d)
  letI actX : MulAction G X :=
    { smul := fun g x => (g * x.1, x.2)
      one_smul := fun x => by
        show ((1 : G) * x.1, x.2) = x
        rw [one_mul]
      mul_smul := fun g g' x => by
        show ((g * g') * x.1, x.2) = (g * (g' * x.1), x.2)
        rw [mul_assoc] }
  refine ⟨{ H := H, X := X, e := e, E := orbitDecompositionLinearEquiv Φ ρ hmono hfree, free := ?_, intertw := ?_ }⟩
  · intro g x hx
    have h1 : g * x.1 = x.1 := congrArg Prod.fst hx
    simpa using h1
  · intro v a φ hmem x
    have hφ : (⟨A.rhoT v a φ, hmem⟩ : A.Mu0) = ρ (Pi.mulSingle v (e v a)) φ := by
      apply Subtype.ext
      exact (hρ v a φ).symm
    rw [hφ, t2xEquiv_apply, t2xEquiv_apply]
    show Φ (ρ x.1 (ρ (Pi.mulSingle v (e v a)) φ)) (Quotient.out x.2.1) x.2.2 =
      Φ (ρ (Pi.mulSingle v (e v a) * x.1) φ) (Quotient.out x.2.1) x.2.2
    rw [mul_comm, map_mul]
    rfl

end ModelOf

theorem free_rank_model_of_diamonds (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf) :
    Nonempty (FreeRankModel (D.mem u).A) := by
  haveI : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  obtain ⟨d, Φ, hΦ⟩ := forms_level_zero_linear_equiv Tf hS
  letI : MulAction ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) ((D.mem u).C.cls 0) :=
    MulAction.compHom _ (t2xAc Tf hE)
  refine free_rank_model_of_free_action (D.mem u).A (fun v => t2xU v) Φ (t2xRho Tf hE) ?_ ?_ ?_
  · intro g c φ h
    rw [hΦ] at h ⊢
    exact zero_of_group_action_zero Tf hE g c φ h
  · intro g c h
    exact group_acts_freely_classes Tf hS hE g c h
  · intro v a φ
    rw [group_rep_mulSingle_eq_rho, MulEquiv.symm_apply_apply]

theorem free_rank_model_of_split (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hs : SplitAtT Tf.atT) :
    Nonempty (FreeRankModel (D.mem u).A) :=
  free_rank_model_of_diamonds Tf hS (diamond_elements_of_split Tf hs)

theorem level_zero_values_ne_bot (Tf : Forms0 D u) : ∃ w ∈ levelZeroValues Tf, w ≠ 0 := by
  set e := (Tf.val 0 (Nat.zero_le _) rfl).eY
  let F : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) → ℂ :=
    Formalism.L2.Col.evV (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ)
      (Formalism.L2.Col.extV ℂ ((D.fm u).lam 0))
  refine ⟨fun y => F (e y), ?_, ?_⟩
  · show (fun z => F (e (e.symm z))) ∈ ValC (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) ((D.fm u).lam 0)
    simp only [Equiv.apply_symm_apply]
    exact Formalism.L2.Col.evV_mem_ValC (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ) _
  · intro h
    apply Formalism.L2.Col.evV_extV_ne_zero (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ) ⟨fun _ => 1, fun _ => by simp⟩
    funext z
    have hz : F (e (e.symm z)) = 0 := congrFun h (e.symm z)
    exact (congrArg F (e.apply_symm_apply z)).symm.trans hz

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
