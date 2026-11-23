import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.Pairing
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ShiftNegOneHomologyIsoSymmHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

namespace LeibnizPairing

section Left

variable {L N' L' : CochainComplex (ModuleCat.{u} k) ℕ} (μL : LeibnizPairing L N' L')

noncomputable def shiftLeft : ∀ (r s n : ℕ), r + s = n →
    shiftNegOneX L r →ₗ[k] N'.X s →ₗ[k] shiftNegOneX L' n
  | 0, _, _, _ => 0
  | _ + 1, _, 0, _ => 0
  | r + 1, s, n + 1, _ => μL.μ (show r + s = n by omega)

theorem shiftLeft_succ {r s n : ℕ} (h : r + 1 + s = n + 1) (y : L.X r) (w : N'.X s) :
    μL.shiftLeft (r + 1) s (n + 1) h (shiftNegOneSucc L r y) w =
      shiftNegOneSucc L' n (μL.μ (by omega) y w) :=
  rfl

theorem shiftLeft_leibniz {r s n : ℕ} (h : r + s = n) (y : shiftNegOneX L r) (w : N'.X s) :
    (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y w) =
      μL.shiftLeft (r + 1) s (n + 1) (by omega) ((shiftNegOneD L r).hom y) w +
        (-1 : k) ^ r • μL.shiftLeft r (s + 1) (n + 1) (by omega) y ((N'.d s (s + 1)).hom w) := by
  cases r with
  | zero =>
    have e1 : μL.shiftLeft 0 s n h y w = 0 := rfl
    have e2 : (shiftNegOneD L 0).hom y = 0 := rfl
    have e3 : μL.shiftLeft 0 (s + 1) (n + 1) (by omega) y ((N'.d s (s + 1)).hom w) = 0 := rfl
    rw [e1, e2, e3, map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  | succ r =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    revert y
    intro (y : L.X r)
    change -(L'.d m (m + 1)).hom (μL.μ (show r + s = m by omega) y w) =
      μL.μ (show r + 1 + s = m + 1 by omega) (-(L.d r (r + 1)).hom y) w +
        (-1 : k) ^ (r + 1) • μL.μ (show r + (s + 1) = m + 1 by omega) y ((N'.d s (s + 1)).hom w)
    rw [μL.leibniz, map_neg, LinearMap.neg_apply, pow_succ, mul_neg_one, neg_smul, neg_add]

variable {K K' N : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'} (ρ : N ⟶ N')
  (μK : LeibnizPairing K N K')

noncomputable def coconeLeftμ {r s n : ℕ} (h : r + s = n) :
    (mappingCoconeNat f).X r →ₗ[k] N.X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun (p : K.X r × shiftNegOneX L r) z =>
      ((μK.μ h p.1 z, μL.shiftLeft r s n h p.2 ((ρ.f s).hom z)) : K'.X n × shiftNegOneX L' n))
    (fun p q z => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun c p z => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun p z z' => Prod.ext (map_add _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (z + z')) = _
      rw [map_add, map_add]
      rfl))
    (fun c p z => Prod.ext (map_smul _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (c • z)) = _
      rw [map_smul, map_smul]
      rfl))

theorem coconeLeftμ_apply {r s n : ℕ} (h : r + s = n) (x : K.X r) (y : shiftNegOneX L r)
    (z : N.X s) :
    coconeLeftμ μL ρ μK (f := f) (f' := f') h ((x, y) : K.X r × shiftNegOneX L r) z =
      ((μK.μ h x z, μL.shiftLeft r s n h y ((ρ.f s).hom z)) : K'.X n × shiftNegOneX L' n) :=
  rfl

noncomputable def coconeLeft (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) :
    LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat f') where
  μ h := coconeLeftμ μL ρ μK h
  leibniz {r s n} h p z := by
    revert p
    intro (p : K.X r × shiftNegOneX L r)
    obtain ⟨x, y⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x z) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) +
        (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y ((ρ.f s).hom z)) =
      μL.shiftLeft (r + 1) s (n + 1) (by omega)
          (shiftNegOneSucc L r ((f.f r).hom x) + (shiftNegOneD L r).hom y) ((ρ.f s).hom z) +
        (-1 : k) ^ r • μL.shiftLeft r (s + 1) (n + 1) (by omega) y
          ((ρ.f (s + 1)).hom ((N.d s (s + 1)).hom z))
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)) z, hc, shiftLeft_leibniz,
      LinearMap.map_add₂, shiftLeft_succ]
    exact (add_assoc _ _ _).symm

variable (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
  (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

end Left

theorem _root_.GroundTheory.ProfCoh.mappingCoconeNat.exists_homologyδ_homologyπ
    {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L) (r : ℕ) (c : L.cycles r) :
    ∃ c' : (mappingCoconeNat f).cycles (r + 1),
      (mappingCoconeNat.homologyδ f r).hom ((L.homologyπ r).hom c) =
        ((mappingCoconeNat f).homologyπ (r + 1)).hom c' ∧
      ((mappingCoconeNat f).iCycles (r + 1)).hom c' =
        (((0 : K.X (r + 1)), shiftNegOneSucc L r ((L.iCycles r).hom c)) :
          K.X (r + 1) × shiftNegOneX L (r + 1)) := by
  let w := ((shiftNegOne L).liftCycles (L.iCycles r ≫ shiftNegOneSuccHom L r) (r + 1 + 1)
    (CochainComplex.next ℕ (r + 1)) (iCycles_shiftNegOneSuccHom_d L r)).hom c
  refine ⟨(HomologicalComplex.cyclesMap (mappingCoconeNat.inr f) (r + 1)).hom w, ?_, ?_⟩
  · change (HomologicalComplex.homologyMap (mappingCoconeNat.inr f) (r + 1)).hom
      ((shiftNegOneHomologyHom L r).hom ((L.homologyπ r).hom c)) = _
    rw [hom_apply_hom_apply_of_comp_eq (homologyπ_shiftNegOneHomologyHom L r) c]
    exact homologyMap_homologyπ_apply _ _ _
  · rw [iCycles_cyclesMap_apply,hom_apply_hom_apply_of_comp_eq ((shiftNegOne L).liftCycles_i _ _ _ _) c]
    rfl

section LeftDelta

variable {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

theorem coconeLeft_homology_homologyδ {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : L.homology r) (z : N.homology s) :
    (coconeLeft μL ρ μK hc).homology h' ((mappingCoconeNat.homologyδ f r).hom ξ) z =
      (mappingCoconeNat.homologyδ f' n).hom
        (μL.homology h ξ ((HomologicalComplex.homologyMap ρ s).hom z)) := by
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ r ξ
  obtain ⟨w, rfl⟩ := homologyπ_hom_surjective _ s z
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f r c
  rw [homologyMap_homologyπ_apply, homology_homologyπ]
  obtain ⟨c'', hc''1, hc''2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' n
    (μL.cycles h c ((HomologicalComplex.cyclesMap ρ s).hom w))
  rw [hc'1, hc''1, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cycles, hc'2, hc''2, iCycles_cycles, iCycles_cyclesMap_apply]
  exact Prod.ext (LinearMap.map_zero₂ _ _) rfl

end LeftDelta

section Right

variable {M' L L' : CochainComplex (ModuleCat.{u} k) ℕ} (μR : LeibnizPairing M' L L')

noncomputable def shiftRight : ∀ (r s n : ℕ), r + s = n →
    M'.X r →ₗ[k] shiftNegOneX L s →ₗ[k] shiftNegOneX L' n
  | _, 0, _, _ => 0
  | _, _ + 1, 0, _ => 0
  | r, s + 1, n + 1, _ => μR.μ (show r + s = n by omega)

theorem shiftRight_succ {r s n : ℕ} (h : r + (s + 1) = n + 1) (u : M'.X r) (c : L.X s) :
    μR.shiftRight r (s + 1) (n + 1) h u (shiftNegOneSucc L s c) =
      shiftNegOneSucc L' n (μR.μ (by omega) u c) :=
  rfl

theorem shiftRight_leibniz {r s n : ℕ} (h : r + s = n) (u : M'.X r) (c : shiftNegOneX L s) :
    (shiftNegOneD L' n).hom (μR.shiftRight r s n h u c) =
      -μR.shiftRight (r + 1) s (n + 1) (by omega) ((M'.d r (r + 1)).hom u) c +
        (-1 : k) ^ r • μR.shiftRight r (s + 1) (n + 1) (by omega) u ((shiftNegOneD L s).hom c) := by
  cases s with
  | zero =>
    have e1 : μR.shiftRight r 0 n h u c = 0 := rfl
    have e2 : (shiftNegOneD L 0).hom c = 0 := rfl
    have e3 : μR.shiftRight (r + 1) 0 (n + 1) (by omega) ((M'.d r (r + 1)).hom u) c = 0 := rfl
    rw [e1, e2, e3, map_zero, map_zero, neg_zero, smul_zero, add_zero]
  | succ s =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    revert c
    intro (c : L.X s)
    change -(L'.d m (m + 1)).hom (μR.μ (show r + s = m by omega) u c) =
      -μR.μ (show r + 1 + s = m + 1 by omega) ((M'.d r (r + 1)).hom u) c +
        (-1 : k) ^ r • μR.μ (show r + (s + 1) = m + 1 by omega) u (-(L.d s (s + 1)).hom c)
    rw [μR.leibniz, map_neg, smul_neg, neg_add]

variable {M K K' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'} (ρ : M ⟶ M')
  (μK : LeibnizPairing M K K')

noncomputable def coconeRightμ {r s n : ℕ} (h : r + s = n) :
    M.X r →ₗ[k] (mappingCoconeNat f).X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun x (p : K.X s × shiftNegOneX L s) =>
      ((μK.μ h x p.1, (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) p.2) :
        K'.X n × shiftNegOneX L' n))
    (fun x x' p => Prod.ext (LinearMap.map_add₂ _ _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom (x + x')) p.2 = _
      rw [map_add, LinearMap.map_add₂, smul_add]
      rfl))
    (fun c x p => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom (c • x)) p.2 = _
      rw [map_smul, LinearMap.map_smul₂, smul_comm]
      rfl))
    (fun x p q => Prod.ext (map_add _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) (p.2 + q.2) = _
      rw [map_add, smul_add]
      rfl))
    (fun c x p => Prod.ext (map_smul _ _ _) (by
      change (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) (c • p.2) = _
      rw [map_smul, smul_comm]
      rfl))

theorem coconeRightμ_apply {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : K.X s)
    (c : shiftNegOneX L s) :
    coconeRightμ μR ρ μK (f := f) (f' := f') h x ((y, c) : K.X s × shiftNegOneX L s) =
      ((μK.μ h x y, (-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) c) :
        K'.X n × shiftNegOneX L' n) :=
  rfl

noncomputable def coconeRight (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : K.X s),
    (f'.f n).hom (μK.μ h x y) = μR.μ h ((ρ.f r).hom x) ((f.f s).hom y)) :
    LeibnizPairing M (mappingCoconeNat f) (mappingCoconeNat f') where
  μ h := coconeRightμ μR ρ μK h
  leibniz {r s n} h x p := by
    revert p
    intro (p : K.X s × shiftNegOneX L s)
    obtain ⟨y, c⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x y) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x y)) +
        (shiftNegOneD L' n).hom ((-1 : k) ^ r • μR.shiftRight r s n h ((ρ.f r).hom x) c) =
      (-1 : k) ^ (r + 1) • μR.shiftRight (r + 1) s (n + 1) (by omega)
          ((ρ.f (r + 1)).hom ((M.d r (r + 1)).hom x)) c +
        (-1 : k) ^ r • ((-1 : k) ^ r • μR.shiftRight r (s + 1) (n + 1) (by omega) ((ρ.f r).hom x)
          (shiftNegOneSucc L s ((f.f s).hom y) + (shiftNegOneD L s).hom c))
    have hsq : (-1 : k) ^ r * (-1 : k) ^ r = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have hs : (-1 : k) ^ (r + 1) = -(-1 : k) ^ r := by rw [pow_succ, mul_neg_one]
    have hpp : ∀ v : shiftNegOneX L' (n + 1), (-1 : k) ^ r • (-1 : k) ^ r • v = v := fun v => by
      rw [smul_smul, hsq, one_smul]
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm r (r + 1)) x, hc, map_smul, shiftRight_leibniz,
      map_add, shiftRight_succ]
    conv_lhs => rw [smul_add, smul_neg, hpp]
    conv_rhs => rw [hpp, hs, neg_smul]
    abel

end Right

end LeibnizPairing

end GroundTheory.ProfCoh
