import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsGat

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

attribute [local irreducible] Formalism.L2.G.repP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

def StabU (L : ColLevel R F E sp gp C A clsLat) (x : GA sp) : Type :=
  {γ : UJ (sp.cm.sig : E →+* E) sp.gram0 // x⁻¹ * ratA sp γ * x ∈ KA L}

def TrivStabU (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ (x : GA sp) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0), x⁻¹ * ratA sp γ * x ∈ KA L → γ = 1

def stabConj (x x' : GA sp) (h0 : UJ (sp.cm.sig : E →+* E) sp.gram0) (κ : GA sp) (hκ : κ ∈ KA L)
    (e : x' = ratA sp h0 * x * κ) : StabU L x ≃ StabU L x' where
  toFun γ := ⟨h0 * γ.1 * h0⁻¹, by
    have : x'⁻¹ * ratA sp (h0 * γ.1 * h0⁻¹) * x' = κ⁻¹ * (x⁻¹ * ratA sp γ.1 * x) * κ := by
      rw [e, map_mul, map_mul, map_inv]; group
    rw [this]
    exact (KA L).mul_mem ((KA L).mul_mem ((KA L).inv_mem hκ) γ.2) hκ⟩
  invFun γ := ⟨h0⁻¹ * γ.1 * h0, by
    have key : ∀ γ0 : UJ (sp.cm.sig : E →+* E) sp.gram0,
        x⁻¹ * ratA sp (h0⁻¹ * γ0 * h0) * x = κ * (x'⁻¹ * ratA sp γ0 * x') * κ⁻¹ := by
      intro γ0
      rw [e, map_mul, map_mul, map_inv]; group
    rw [key]
    exact (KA L).mul_mem ((KA L).mul_mem hκ γ.2) ((KA L).inv_mem hκ)⟩
  left_inv γ := Subtype.ext (by show h0⁻¹ * (h0 * γ.1 * h0⁻¹) * h0 = γ.1; group)
  right_inv γ := Subtype.ext (by show h0 * (h0⁻¹ * γ.1 * h0) * h0⁻¹ = γ.1; group)

def stabRec (c : C.cls 0) : C.stab 0 c ≃ StabU L (L.y c) :=
  Equiv.ofBijective (fun s => ⟨L.stabI c s, by
      have h := (L.stabI_range c (L.stabI c s : GL (Fin R.k) E) (L.stabI c s).2).1 ⟨s, rfl⟩
      exact (mem_map_conj L.U _ _).1 h⟩)
    ⟨fun a b hab => L.stabI_inj c (congrArg Subtype.val hab), fun γ => by
      obtain ⟨s, hs⟩ := (L.stabI_range c (γ.1 : GL (Fin R.k) E) γ.1.2).2 ((mem_map_conj L.U _ _).2 γ.2)
      exact ⟨s, Subtype.ext hs⟩⟩

def clsOf (L : ColLevel R F E sp gp C A clsLat) (c : ClassSet (HA sp) (KA L)) : C.cls 0 :=
  (Equiv.ofBijective _ L.y_bij).symm c

theorem clsOf_spec (c : ClassSet (HA sp) (KA L)) : Fib.mkC (HA sp) (KA L) (L.y (clsOf L c)) = c :=
  (Equiv.ofBijective _ L.y_bij).apply_symm_apply c

theorem clsOf_inj : Function.Injective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.injective

theorem clsOf_surj : Function.Surjective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.surjective

theorem card_stabU (x : GA sp) : Nat.card (StabU L x) = Nat.card (C.stab 0 (clsOf L (Fib.mkC (HA sp) (KA L) x))) := by
  obtain ⟨h, hh, κ, hκ, e⟩ := (Fib.mk_eq_iff (HA sp) (KA L) _ _).1 (clsOf_spec (L := L) (Fib.mkC (HA sp) (KA L) x))
  obtain ⟨h0, rfl⟩ := exists_ratA h hh
  exact (Nat.card_congr ((stabRec _).trans (stabConj _ x h0 κ hκ e))).symm

theorem trivStabU_of_rec (h : ∀ c : C.cls 0, Nat.card (C.stab 0 c) = 1) : TrivStabU L := by
  intro x γ hγ
  have h1 : Nat.card (StabU L x) = 1 := by rw [card_stabU, h]
  have h2 : Subsingleton (StabU L x) := (Nat.card_eq_one_iff_unique.1 h1).1
  have h3 : x⁻¹ * ratA sp (1 : UJ (sp.cm.sig : E →+* E) sp.gram0) * x ∈ KA L := by
    rw [map_one, mul_one, inv_mul_cancel]; exact (KA L).one_mem
  exact congrArg Subtype.val (h2.elim (⟨γ, hγ⟩ : StabU L x) ⟨1, h3⟩)

variable (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)

include hH in

theorem fix_iff (i : compL L p) (g : Fin nV → GL (Fin (m + 1)) Qq) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    (repP L p i * jQ I hdet hk g)⁻¹ * ratA sp γ * (repP L p i * jQ I hdet hk g) ∈ KA L ↔
      γ ∈ gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (repP L p i).1 ∧
        (fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v)) = tupOf W g := by
  refine ((fibP I hdet hk hH).stab_iff (HA sp) (repP L p) (prP_repP I hk) i g (ratA sp γ)).trans
    (and_congr (mem_gamC_iff (repP L p i) γ).symm ?_)
  show g⁻¹ * (prP I hk (ratA sp γ) * g) ∈ _ ↔ _
  rw [← tupOf_eq_iff]
  have : tupOf W (prP I hk (ratA sp γ) * g) = fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v) := by
    funext v
    exact gMap_mul W _ _ _
  rw [this]

include hH in

def fixEquiv (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y = (repP L p i).1)
    (g : Fin nV → GL (Fin (m + 1)) Qq) :
    {γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y //
      (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ (tupOf W g) = tupOf W g} ≃
      StabU L (repP L p i * jQ I hdet hk g) where
  toFun γ := ⟨γ.1.1, (fix_iff hk I hdet hH i g γ.1.1).2 ⟨hy ▸ γ.1.2, by
    have := γ.2
    rwa [level_action_lattice_eq] at this⟩⟩
  invFun γ := ⟨⟨γ.1, hy ▸ ((fix_iff hk I hdet hH i g γ.1).1 γ.2).1⟩, by
    rw [level_action_lattice_eq]
    exact ((fix_iff hk I hdet hH i g γ.1).1 γ.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Formalism.L2.G.Cmp
