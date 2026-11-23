import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

theorem hom_apply_hom_apply_of_comp_eq {k : Type u} [CommRing k] {X Y Z : ModuleCat.{u} k}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) : g.hom (f.hom x) = h.hom x := by
  rw [← e]
  rfl

theorem hom_apply_hom_apply_eq_of_comp_eq {k : Type u} [CommRing k] {X Y Y' Z : ModuleCat.{u} k}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z} (e : f ≫ g = f' ≫ g') (x : X) :
    g.hom (f.hom x) = g'.hom (f'.hom x) := by
  rw [hom_apply_hom_apply_of_comp_eq e x]
  rfl

section Cocone

variable {k : Type u} [CommRing k]

noncomputable def shiftNegOneX (L : CochainComplex (ModuleCat.{u} k) ℕ) : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k PUnit
  | n + 1 => L.X n

noncomputable def shiftNegOneD (L : CochainComplex (ModuleCat.{u} k) ℕ) :
    ∀ n, shiftNegOneX L n ⟶ shiftNegOneX L (n + 1)
  | 0 => 0
  | n + 1 => -L.d n (n + 1)

theorem shiftNegOneD_succ_apply (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) (y : L.X n) :
    (shiftNegOneD L (n + 1)).hom y = -(L.d n (n + 1)).hom y :=
  rfl

theorem shiftNegOneD_comp (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    shiftNegOneD L n ≫ shiftNegOneD L (n + 1) = 0 := by
  cases n with
  | zero => exact Limits.zero_comp
  | succ n =>
    exact (Preadditive.neg_comp_neg _ _).trans (L.d_comp_d _ _ _)

theorem shiftNegOneD_shiftNegOneD_apply (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ)
    (y : shiftNegOneX L n) : (shiftNegOneD L (n + 1)).hom ((shiftNegOneD L n).hom y) = 0 :=
  hom_apply_hom_apply_of_comp_eq (shiftNegOneD_comp L n) y

noncomputable def shiftNegOne (L : CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (shiftNegOneX L) (shiftNegOneD L) (shiftNegOneD_comp L)

theorem shiftNegOne_d (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (shiftNegOne L).d n (n + 1) = shiftNegOneD L n :=
  CochainComplex.of_d _ _ n

def shiftNegOneSucc (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    L.X n →ₗ[k] shiftNegOneX L (n + 1) :=
  LinearMap.id

theorem shiftNegOneSucc_apply (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) (y : L.X n) :
    shiftNegOneSucc L n y = y :=
  rfl

variable (K L : CochainComplex (ModuleCat.{u} k) ℕ)

noncomputable abbrev mappingCoconeNatX (n : ℕ) : ModuleCat.{u} k :=
  ModuleCat.of k (K.X n × shiftNegOneX L n)

variable {K L} (f : K ⟶ L)

noncomputable def mappingCoconeNatD (n : ℕ) :
    mappingCoconeNatX K L n ⟶ mappingCoconeNatX K L (n + 1) :=
  ModuleCat.ofHom (((K.d n (n + 1)).hom.comp (LinearMap.fst k _ _)).prod
    ((shiftNegOneSucc L n).comp ((f.f n).hom.comp (LinearMap.fst k _ _)) +
      (shiftNegOneD L n).hom.comp (LinearMap.snd k _ _)))

theorem mappingCoconeNatD_apply (n : ℕ) (x : K.X n) (y : shiftNegOneX L n) :
    (mappingCoconeNatD f n).hom (x, y) =
      ((K.d n (n + 1)).hom x, shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom y) :=
  rfl

theorem mappingCoconeNatD_comp (n : ℕ) :
    mappingCoconeNatD f n ≫ mappingCoconeNatD f (n + 1) = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
  obtain ⟨x, y⟩ := p
  change (mappingCoconeNatD f (n + 1)).hom ((mappingCoconeNatD f n).hom (x, y)) = 0
  rw [mappingCoconeNatD_apply, mappingCoconeNatD_apply]
  refine Prod.ext (hom_apply_hom_apply_of_comp_eq (K.d_comp_d _ _ _) x) ?_
  change shiftNegOneSucc L (n + 1) ((f.f (n + 1)).hom ((K.d n (n + 1)).hom x)) +
    (shiftNegOneD L (n + 1)).hom (shiftNegOneSucc L n ((f.f n).hom x) +
      (shiftNegOneD L n).hom y) = 0
  rw [map_add, shiftNegOneD_shiftNegOneD_apply, add_zero, shiftNegOneSucc_apply,
    shiftNegOneSucc_apply, shiftNegOneD_succ_apply]
  change ((f.f (n + 1)).hom ((K.d n (n + 1)).hom x) : L.X (n + 1)) +
    -(L.d n (n + 1)).hom ((f.f n).hom x) = 0
  rw [← hom_apply_hom_apply_eq_of_comp_eq (f.comm n (n + 1)) x]
  exact add_neg_cancel _

noncomputable def mappingCoconeNat : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (mappingCoconeNatX K L) (mappingCoconeNatD f) (mappingCoconeNatD_comp f)

theorem mappingCoconeNat_d (n : ℕ) :
    (mappingCoconeNat f).d n (n + 1) = mappingCoconeNatD f n :=
  CochainComplex.of_d _ _ n

noncomputable def mappingCoconeNat.fst : mappingCoconeNat f ⟶ K :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.fst k (K.X n) (shiftNegOneX L n)))
    fun n => by
      rw [mappingCoconeNat_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

noncomputable def mappingCoconeNat.inr : shiftNegOne L ⟶ mappingCoconeNat f :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.inr k (K.X n) (shiftNegOneX L n)))
    fun n => by
      rw [mappingCoconeNat_d, shiftNegOne_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun y => Prod.ext ?_ ?_)
      · exact (K.d n (n + 1)).hom.map_zero
      · show shiftNegOneSucc L n ((f.f n).hom 0) + (shiftNegOneD L n).hom y =
          (shiftNegOneD L n).hom y
        rw [map_zero, map_zero, zero_add]

end Cocone

section Pi

variable {k : Type u} [CommRing k] {ι : Type u}

noncomputable def piComplex (K : ι → CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (∀ v, (K v).X n))
    (fun n => ModuleCat.ofHom (LinearMap.pi fun v => ((K v).d n (n + 1)).hom.comp (LinearMap.proj v)))
    fun _ => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun v =>
      hom_apply_hom_apply_of_comp_eq ((K v).d_comp_d _ _ _) (x v))

theorem piComplex_d (K : ι → CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (piComplex K).d n (n + 1) = ModuleCat.ofHom
      (LinearMap.pi fun v => ((K v).d n (n + 1)).hom.comp (LinearMap.proj v)) :=
  by
  unfold piComplex
  exact CochainComplex.of_d (V := ModuleCat.{u} k) (fun n => ModuleCat.of k (∀ v, (K v).X n))
    (fun n => ModuleCat.ofHom (LinearMap.pi fun v => ((K v).d n (n + 1)).hom.comp (LinearMap.proj v)))
    n

theorem piComplex_d_hom_apply (K : ι → CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ)
    (x : (piComplex K).X n) (v : ι) :
    ((piComplex K).d n (n + 1)).hom x v = ((K v).d n (n + 1)).hom (x v) := by
  rw [piComplex_d]
  rfl

noncomputable def piLift {M : CochainComplex (ModuleCat.{u} k) ℕ}
    {K : ι → CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, M ⟶ K v) : M ⟶ piComplex K :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.pi fun v => ((g v).f n).hom))
    fun n => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun v => by
      change ((piComplex K).d n (n + 1)).hom _ v = ((g v).f (n + 1)).hom ((M.d n (n + 1)).hom x)
      rw [piComplex_d_hom_apply]
      exact hom_apply_hom_apply_eq_of_comp_eq ((g v).comm n (n + 1)) x)

end Pi

section CompactSupport

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)]

omit [IsTopologicalGroup G] in

theorem continuous_toMonoidHom {H' : Type u} [Group H'] [TopologicalSpace H'] (ψ : H' →ₜ* G) :
    Continuous ψ.toMonoidHom :=
  ψ.continuous_toFun

instance isDiscreteRep_res_toMonoidHom {H' : Type u} [Group H'] [TopologicalSpace H']
    (ψ : H' →ₜ* G) (A : Rep.{u} k G) [IsDiscreteRep A] : IsDiscreteRep (Rep.res ψ.toMonoidHom A) :=
  IsDiscreteRep.res (continuous_toMonoidHom ψ) A

variable (φ : ∀ v, H v →ₜ* G) (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)

noncomputable def localRes :
    cochainsComplex A ⟶ piComplex fun v => cochainsComplex (Aᵥ v) :=
  piLift fun v => cochainsMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (a v)

noncomputable def compactCochains : CochainComplex (ModuleCat.{u} k) ℕ :=
  mappingCoconeNat (localRes φ A Aᵥ a)

noncomputable def compactCohomology (n : ℕ) : ModuleCat.{u} k :=
  (compactCochains φ A Aᵥ a).homology n

noncomputable abbrev compactCohomologyRes (n : ℕ) : ModuleCat.{u} k :=
  compactCohomology φ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _) n

end CompactSupport

end GroundTheory.ProfCoh
