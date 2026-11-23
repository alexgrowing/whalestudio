import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConePairing
import GroundTheory.ProfiniteCohomology.MackeyFormula.ConeHomotopy
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k : Type u} [CommRing k]

namespace mappingCoconeNat

section Cocycles

variable {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)

theorem f_fst_eq_d_snd_of_d_eq_zero {n : ℕ} (p : (mappingCoconeNat f).X (n + 1))
    (hp : ((mappingCoconeNat f).d (n + 1) (n + 1 + 1)).hom p = 0) :
    (f.f (n + 1)).hom p.1 = (L.d n (n + 1)).hom (p.2 : L.X n) := by
  rw [mappingCoconeNat_d] at hp
  have h2 := congrArg Prod.snd hp
  change ((f.f (n + 1)).hom p.1 : L.X (n + 1)) + -(L.d n (n + 1)).hom (p.2 : L.X n) = 0 at h2
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

theorem f_fst_eq_zero_of_d_eq_zero (p : (mappingCoconeNat f).X 0)
    (hp : ((mappingCoconeNat f).d 0 1).hom p = 0) :
    (f.f 0).hom p.1 = 0 := by
  rw [mappingCoconeNat_d] at hp
  have h2 := congrArg Prod.snd hp
  change ((f.f 0).hom p.1 : L.X 0) + 0 = 0 at h2
  rwa [add_zero] at h2

end Cocycles

section Product

variable {KA LA KC LC N LN KA' LA' KC' LC' N' LN' : CochainComplex (ModuleCat.{u} k) ℕ}
  {fA : KA ⟶ LA} {fC : KC ⟶ LC} {ρ : N ⟶ LN}
  {fA' : KA' ⟶ LA'} {fC' : KC' ⟶ LC'} {ρ' : N' ⟶ LN'}
  {αA : KA ⟶ KA'} {βA : LA ⟶ LA'} {αC : KC ⟶ KC'} {βC : LC ⟶ LC'} {αN : N ⟶ N'}
  {βN : LN ⟶ LN'}
  (hA : Homotopy (fA ≫ βA) (αA ≫ fA')) (hC : Homotopy (fC ≫ βC) (αC ≫ fC'))
  (hN : Homotopy (ρ ≫ βN) (αN ≫ ρ'))
  (μL : LeibnizPairing LA LN LC) (μK : LeibnizPairing KA N KC)
  (μL' : LeibnizPairing LA' LN' LC') (μK' : LeibnizPairing KA' N' KC')

include hN in

theorem homotopy_apply_zero_of_d_eq_zero (z : N.X 0) (hz : (N.d 0 1).hom z = 0) :
    (βN.f 0).hom ((ρ.f 0).hom z) = (ρ'.f 0).hom ((αN.f 0).hom z) := by
  have e := congrArg (fun φ => φ.hom z) (hN.comm 0)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_add, LinearMap.add_apply] at e
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex] at e
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero, ModuleCat.hom_zero,
    LinearMap.zero_apply, zero_add] at e
  exact e

theorem homotopy_apply_succ_of_d_eq_zero (l : ℕ) (z : N.X (l + 1))
    (hz : (N.d (l + 1) (l + 1 + 1)).hom z = 0) :
    (βN.f (l + 1)).hom ((ρ.f (l + 1)).hom z) =
      (LN'.d l (l + 1)).hom ((hN.hom (l + 1) l).hom z) + (ρ'.f (l + 1)).hom ((αN.f (l + 1)).hom z) := by
  have e := congrArg (fun φ => φ.hom z) (hN.comm (l + 1))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_add, LinearMap.add_apply] at e
  rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex] at e
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero, zero_add] at e
  exact e

theorem snd_sub_eq_neg_d (hβ : ∀ {r s n : ℕ} (h : r + s = n) (y : LA.X r) (w : LN.X s),
      (βC.f n).hom (μL.μ h y w) = μL'.μ h ((βA.f r).hom y) ((βN.f s).hom w))
    (hh : ∀ {r s m : ℕ} (h : r + 1 + (s + 1) = m + 1) (x : KA.X (r + 1)) (z : N.X (s + 1)),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show r + (s + 1) = m by omega) ((hA.hom (r + 1) r).hom x)
            ((ρ'.f (s + 1)).hom ((αN.f (s + 1)).hom z)) +
          (-1 : k) ^ (r + 1) • μL'.μ (show r + 1 + s = m by omega)
            ((βA.f (r + 1)).hom ((fA.f (r + 1)).hom x)) ((hN.hom (s + 1) s).hom z))
    (j l : ℕ) (h : j + 1 + (l + 1) = j + l + 1 + 1) (a : KA.X (j + 1)) (b : LA.X j)
    (z : N.X (l + 1)) (hab : (fA.f (j + 1)).hom a = (LA.d j (j + 1)).hom b)
    (hz : (N.d (l + 1) (l + 1 + 1)).hom z = 0) :
    (βC.f (j + l + 1)).hom (μL.μ (show j + (l + 1) = j + l + 1 by omega) b ((ρ.f (l + 1)).hom z)) -
        (hC.hom (j + l + 1 + 1) (j + l + 1)).hom (μK.μ h a z) -
        μL'.μ (show j + (l + 1) = j + l + 1 by omega)
          ((βA.f j).hom b - (hA.hom (j + 1) j).hom a) ((ρ'.f (l + 1)).hom ((αN.f (l + 1)).hom z)) =
      -(LC'.d (j + l) (j + l + 1)).hom ((-1 : k) ^ (j + 1) •
        μL'.μ (show j + l = j + l from rfl) ((βA.f j).hom b) ((hN.hom (l + 1) l).hom z)) := by
  rw [hβ, homotopy_apply_succ_of_d_eq_zero hN l z hz, hh h a z, map_smul, μL'.leibniz,
    hom_apply_hom_apply_eq_of_comp_eq (βA.comm j (j + 1)) b, ← hab]
  simp only [map_add, map_sub, LinearMap.sub_apply, smul_add, smul_smul, ← pow_add]
  have e : (-1 : k) ^ (j + 1 + j) = -1 := by
    rw [show j + 1 + j = 2 * j + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [e, neg_one_smul]
  abel

theorem _root_.GroundTheory.ProfCoh.homologyπ_eq_of_iCycles_sub_eq_d (P : CochainComplex (ModuleCat.{u} k) ℕ)
    {m : ℕ} (a b : P.cycles (m + 1)) (c : P.X m)
    (h : (P.iCycles (m + 1)).hom a - (P.iCycles (m + 1)).hom b = (P.d m (m + 1)).hom c) :
    (P.homologyπ (m + 1)).hom a = (P.homologyπ (m + 1)).hom b := by
  have e : a - b = (P.toCycles m (m + 1)).hom c :=
    iCycles_hom_injective P (m + 1) (by rw [map_sub, h, iCycles_toCycles_hom_apply])
  rw [← sub_eq_zero, ← map_sub, e, homologyπ_toCycles_hom_apply]

theorem homologyMap_mapOfHomotopy_coconeLeft
    (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (z : N.X s),
      (fC.f n).hom (μK.μ h x z) = μL.μ h ((fA.f r).hom x) ((ρ.f s).hom z))
    (hc' : ∀ {r s n : ℕ} (h : r + s = n) (x : KA'.X r) (z : N'.X s),
      (fC'.f n).hom (μK'.μ h x z) = μL'.μ h ((fA'.f r).hom x) ((ρ'.f s).hom z))
    (hα : ∀ {r s n : ℕ} (h : r + s = n) (x : KA.X r) (z : N.X s),
      (αC.f n).hom (μK.μ h x z) = μK'.μ h ((αA.f r).hom x) ((αN.f s).hom z))
    (hβ : ∀ {r s n : ℕ} (h : r + s = n) (y : LA.X r) (w : LN.X s),
      (βC.f n).hom (μL.μ h y w) = μL'.μ h ((βA.f r).hom y) ((βN.f s).hom w))
    (hh : ∀ {r s m : ℕ} (h : r + 1 + (s + 1) = m + 1) (x : KA.X (r + 1)) (z : N.X (s + 1)),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show r + (s + 1) = m by omega) ((hA.hom (r + 1) r).hom x)
            ((ρ'.f (s + 1)).hom ((αN.f (s + 1)).hom z)) +
          (-1 : k) ^ (r + 1) • μL'.μ (show r + 1 + s = m by omega)
            ((βA.f (r + 1)).hom ((fA.f (r + 1)).hom x)) ((hN.hom (s + 1) s).hom z))
    (hh₀ : ∀ {s m : ℕ} (h : 0 + (s + 1) = m + 1) (x : KA.X 0) (z : N.X (s + 1)),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show 0 + s = m by omega) ((βA.f 0).hom ((fA.f 0).hom x)) ((hN.hom (s + 1) s).hom z))
    (hh₁ : ∀ {r m : ℕ} (h : r + 1 + 0 = m + 1) (x : KA.X (r + 1)) (z : N.X 0),
      (hC.hom (m + 1) m).hom (μK.μ h x z) =
        μL'.μ (show r + 0 = m by omega) ((hA.hom (r + 1) r).hom x)
          ((ρ'.f 0).hom ((αN.f 0).hom z)))
    {r s n : ℕ} (h : r + s = n) (x : (mappingCoconeNat fA).homology r) (z : N.homology s) :
    (HomologicalComplex.homologyMap (mapOfHomotopy hC) n).hom
        ((LeibnizPairing.coconeLeft μL ρ μK hc).homology h x z) =
      (LeibnizPairing.coconeLeft μL' ρ' μK' hc').homology h
        ((HomologicalComplex.homologyMap (mapOfHomotopy hA) r).hom x)
        ((HomologicalComplex.homologyMap αN s).hom z) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨z, rfl⟩ := homologyπ_hom_surjective _ s z
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  have hx := iCycles_d_apply _ r (r + 1) x
  have hz := iCycles_d_apply _ s (s + 1) z
  have eL : ((mappingCoconeNat fC').iCycles n).hom (HomologicalComplex.cyclesMap
      (mapOfHomotopy hC) n ((LeibnizPairing.coconeLeft μL ρ μK hc).cycles h x z)) =
      (mapOfHomotopyF hC n).hom (LeibnizPairing.coconeLeftμ μL ρ μK h
        (((mappingCoconeNat fA).iCycles r).hom x) ((N.iCycles s).hom z)) := by
    rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles]
    rfl
  have eR : ((mappingCoconeNat fC').iCycles n).hom
      ((LeibnizPairing.coconeLeft μL' ρ' μK' hc').cycles h
        (HomologicalComplex.cyclesMap (mapOfHomotopy hA) r x)
        (HomologicalComplex.cyclesMap αN s z)) =
      LeibnizPairing.coconeLeftμ μL' ρ' μK' h
        ((mapOfHomotopyF hA r).hom (((mappingCoconeNat fA).iCycles r).hom x))
        ((αN.f s).hom ((N.iCycles s).hom z)) := by
    rw [LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
    rfl
  generalize ((mappingCoconeNat fA).iCycles r).hom x = p at hx eL eR
  generalize (N.iCycles s).hom z = w at hz eL eR
  revert p
  intro (p : KA.X r × shiftNegOneX LA r) hx eL eR
  obtain ⟨a, b⟩ := p
  rcases n with _ | m
  · obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := by omega
    congr 1
    apply iCycles_hom_injective
    rw [eL, eR]
    exact Prod.ext (hα h a w) (Subsingleton.elim (α := PUnit) _ _)
  · rcases r with _ | j
    · obtain rfl : s = m + 1 := by omega
      refine homologyπ_eq_of_iCycles_sub_eq_d _ _ _ 0 ?_
      rw [map_zero, sub_eq_zero, eL, eR]
      refine Prod.ext (hα h a w) ?_
      change (βC.f m).hom 0 - (hC.hom (m + 1) m).hom (μK.μ h a w) = 0
      rw [map_zero, zero_sub, neg_eq_zero, hh₀ h, f_fst_eq_zero_of_d_eq_zero fA (a, b) hx, map_zero,
        map_zero, LinearMap.zero_apply]
    · rcases s with _ | l
      · obtain rfl : m = j := by omega
        obtain ⟨b', rfl⟩ : ∃ b' : LA.X m, b' = b := ⟨b, rfl⟩
        refine homologyπ_eq_of_iCycles_sub_eq_d _ _ _ 0 ?_
        rw [map_zero, sub_eq_zero, eL, eR]
        refine Prod.ext (hα h a w) ?_
        change (βC.f m).hom (μL.μ (show m + 0 = m by omega) b' ((ρ.f 0).hom w)) -
            (hC.hom (m + 1) m).hom (μK.μ h a w) =
          μL'.μ (show m + 0 = m by omega) ((βA.f m).hom b' - (hA.hom (m + 1) m).hom a)
            ((ρ'.f 0).hom ((αN.f 0).hom w))
        rw [hβ, homotopy_apply_zero_of_d_eq_zero hN w hz, hh₁ h, map_sub, LinearMap.sub_apply]
      · obtain rfl : m = j + l + 1 := by omega
        obtain ⟨b', rfl⟩ : ∃ b' : LA.X j, b' = b := ⟨b, rfl⟩
        refine homologyπ_eq_of_iCycles_sub_eq_d _ _ _ ((0 : KC'.X (j + l + 1)), ((-1 : k) ^ (j + 1) •
          μL'.μ (show j + l = j + l from rfl) ((βA.f j).hom b')
            ((hN.hom (l + 1) l).hom w) : LC'.X (j + l))) ?_
        rw [eL, eR, mappingCoconeNat_d]
        refine Prod.ext ?_ ?_
        · change (αC.f _).hom (μK.μ h a w) - μK'.μ h ((αA.f _).hom a) ((αN.f _).hom w) =
            (KC'.d _ _).hom 0
          rw [map_zero, hα, sub_self]
        · change (βC.f (j + l + 1)).hom (μL.μ (show j + (l + 1) = j + l + 1 by omega)
                b' ((ρ.f (l + 1)).hom w)) -
              (hC.hom (j + l + 1 + 1) (j + l + 1)).hom (μK.μ h a w) -
              μL'.μ (show j + (l + 1) = j + l + 1 by omega)
                ((βA.f j).hom b' - (hA.hom (j + 1) j).hom a)
                ((ρ'.f (l + 1)).hom ((αN.f (l + 1)).hom w)) =
            (fC'.f (j + l + 1)).hom 0 + -(LC'.d (j + l) (j + l + 1)).hom ((-1 : k) ^ (j + 1) •
              μL'.μ (show j + l = j + l from rfl) ((βA.f j).hom b')
                ((hN.hom (l + 1) l).hom w))
          rw [map_zero, zero_add]
          exact snd_sub_eq_neg_d hA hC hN μL μK μL' hβ hh j l h a b' w
            (f_fst_eq_d_snd_of_d_eq_zero fA (a, b') hx) hz

end Product

end mappingCoconeNat

end GroundTheory.ProfCoh
