import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CompactCupEqCompactCupRight
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

section Abstract

variable {k : Type u} [CommRing k] {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L}
  {f' : K' ⟶ L'} (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

omit [CommRing k] in
theorem mappingCoconeNat_d_hom_apply' {k : Type u} [CommRing k] {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)
    (n : ℕ) (x : K.X n) (y : shiftNegOneX L n) :
    ((mappingCoconeNat f).d n (n + 1)).hom ((x, y) : K.X n × shiftNegOneX L n) =
      (((K.d n (n + 1)).hom x, shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom y) :
        K.X (n + 1) × shiftNegOneX L (n + 1)) := by
  rw [mappingCoconeNat_d]
  rfl

theorem LeibnizPairing.coconeLeft_homology_eq_homologyδ {p s m : ℕ} (h : p + 1 + s = m + 1)
    (X : (mappingCoconeNat f).cycles (p + 1)) (e : N.cycles s) (q : K'.X m) (w : L'.cycles m)
    (hq : (K'.d m (m + 1)).hom q = μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e))
    (hw : (L'.iCycles m).hom w =
      μL.μ (show p + s = m by omega) (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
        ((ρ.f s).hom ((N.iCycles s).hom e)) - (f'.f m).hom q) :
    (LeibnizPairing.coconeLeft μL ρ μK hc).homology h (((mappingCoconeNat f).homologyπ (p + 1)).hom X)
        ((N.homologyπ s).hom e) =
      (mappingCoconeNat.homologyδ f' m).hom ((L'.homologyπ m).hom w) := by
  rw [LeibnizPairing.homology_homologyπ]
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' m w
  rw [hc'1]
  have key : (LeibnizPairing.coconeLeft μL ρ μK hc).cycles h X e =
      c' + ((mappingCoconeNat f').toCycles m (m + 1)).hom ((q, 0) : K'.X m × shiftNegOneX L' m) := by
    apply iCycles_hom_injective
    have e1 := LeibnizPairing.iCycles_cycles (LeibnizPairing.coconeLeft μL ρ μK hc) h X e
    have e2 := iCycles_toCycles_hom_apply (mappingCoconeNat f') m (m + 1)
      ((q, 0) : K'.X m × shiftNegOneX L' m)
    rw [map_add, e1, e2, mappingCoconeNat_d_hom_apply']
    refine Prod.ext ?_ ?_
    · change μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e) =
        (((mappingCoconeNat f').iCycles (m + 1)).hom c').1 + (K'.d m (m + 1)).hom q
      rw [show (((mappingCoconeNat f').iCycles (m + 1)).hom c').1 = 0 from congrArg Prod.fst hc'2, zero_add, hq]
    · change μL.μ (show p + s = m by omega) (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
          ((ρ.f s).hom ((N.iCycles s).hom e)) =
        (((mappingCoconeNat f').iCycles (m + 1)).hom c').2 +
          (shiftNegOneSucc L' m ((f'.f m).hom q) + (shiftNegOneD L' m).hom 0)
      rw [show (((mappingCoconeNat f').iCycles (m + 1)).hom c').2 =
          shiftNegOneSucc L' m ((L'.iCycles m).hom w) from congrArg Prod.snd hc'2, map_zero, add_zero,
        shiftNegOneSucc_apply, shiftNegOneSucc_apply, hw]
      exact (sub_add_cancel _ _).symm
  rw [key, map_add]
  exact (congrArg (_ + ·) (homologyπ_toCycles_hom_apply (mappingCoconeNat f') m (m + 1)
    ((q, 0) : K'.X m × shiftNegOneX L' m))).trans (add_zero _)

end Abstract

section Compact

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}

theorem compactCup_homologyπ_eq_homologyδ (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
      resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
    {p s m : ℕ} (h : p + 1 + s = m + 1) (X : (compactCochains φ A Aᵥ a).cycles (p + 1))
    (e : (cochainsComplex B).cycles s) (q : (cochainsComplex C).X m)
    (w : (piComplex fun v => cochainsComplex (Cᵥ v)).cycles m)
    (hq : ((cochainsComplex C).d m (m + 1)).hom q = cupPairingCochains μ h
      (((compactCochains φ A Aᵥ a).iCycles (p + 1)).hom X).1 (((cochainsComplex B).iCycles s).hom e))
    (hw : ((piComplex fun v => cochainsComplex (Cᵥ v)).iCycles m).hom w =
      (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ (show p + s = m by omega)
        (show (piComplex fun v => cochainsComplex (Aᵥ v)).X p from
          (((compactCochains φ A Aᵥ a).iCycles (p + 1)).hom X).2)
        (((localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) fun _ => 𝟙 _).f s).hom
          (((cochainsComplex B).iCycles s).hom e)) -
      ((localRes φ C Cᵥ c).f m).hom q) :
    compactCup φ μ μᵥ hμ h (((compactCochains φ A Aᵥ a).homologyπ (p + 1)).hom X)
        (((cochainsComplex B).homologyπ s).hom e) =
      (mappingCoconeNat.homologyδ (localRes φ C Cᵥ c) m).hom
        (((piComplex fun v => cochainsComplex (Cᵥ v)).homologyπ m).hom w) :=
  LeibnizPairing.coconeLeft_homology_eq_homologyδ _ _ _ (localRes_cupPairingCochains φ μ μᵥ hμ) h X e q w hq hw

omit [IsDiscreteRep A] [IsDiscreteRep B] [∀ v, IsDiscreteRep (Aᵥ v)] in

theorem homologyδ_homologyπ_eq_localToCompact {m : ℕ}
    (w : (piComplex fun v => cochainsComplex (Cᵥ v)).cycles m) :
    (mappingCoconeNat.homologyδ (localRes φ C Cᵥ c) m).hom
        (((piComplex fun v => cochainsComplex (Cᵥ v)).homologyπ m).hom w) =
      (localToCompact φ C Cᵥ c m).hom (fun v => ((cochainsComplex (Cᵥ v)).homologyπ m).hom
        ((HomologicalComplex.cyclesMap (piProj (fun v => cochainsComplex (Cᵥ v)) v) m).hom w)) := by
  have e : (localCohomologyIso Cᵥ m).hom.hom
      (((piComplex fun v => cochainsComplex (Cᵥ v)).homologyπ m).hom w) =
      fun v => ((cochainsComplex (Cᵥ v)).homologyπ m).hom
        ((HomologicalComplex.cyclesMap (piProj (fun v => cochainsComplex (Cᵥ v)) v) m).hom w) :=
    funext fun v => (piHomologyIso_hom_apply _ m _ v).trans (homologyMap_homologyπ_apply _ m w)
  rw [← e, localToCompact]
  exact (hom_apply_hom_apply_of_comp_eq (Iso.hom_inv_id_assoc (localCohomologyIso Cᵥ m) _) _).symm

end Compact

end GroundTheory.ProfCoh
