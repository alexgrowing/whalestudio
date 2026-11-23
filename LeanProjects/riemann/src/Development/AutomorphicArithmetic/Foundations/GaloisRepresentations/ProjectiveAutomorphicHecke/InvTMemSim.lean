import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

theorem invT_val {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : (invT n R g).val = (g⁻¹).valᵀ := rfl

@[simp] theorem invT_invT' {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  rw [invT_val, ← map_inv, invT_val, inv_inv, transpose_transpose]

theorem invT_mem_Sim {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {i : B →+* A} {n : ℕ} {p : GL (Fin n) A × Bˣ}
    (h : p ∈ Sim σ i n) : (invT n A p.1, p.2⁻¹) ∈ Sim σ i n := by
  have h1 := mem_Sim.1 h
  have h2 : p.1.valᵀ * p.1.val.map σ = i p.2 • (1 : Matrix (Fin n) (Fin n) A) := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_smul, transpose_one] at this
  have h3 : i (p.2⁻¹ : Bˣ) * i p.2 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h4 : (p.1⁻¹).valᵀ * p.1.valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have h5 : (p.1⁻¹).val.map σ * p.1.val.map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h6 : p.1.val.map σ = i p.2 • (p.1⁻¹).valᵀ := by
    rw [← Matrix.one_mul (p.1.val.map σ), ← h4, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one]
  refine mem_Sim.2 ?_
  show (((p.1⁻¹).valᵀ).map σ)ᵀ * (p.1⁻¹).valᵀ = i (p.2⁻¹ : Bˣ) • 1
  rw [transpose_map, transpose_transpose, ← h5, h6, Matrix.mul_smul, smul_smul, h3, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def th : GUf E n →* GUf E n :=
  (((invT n (Af E)).prodMap invMonoidHom).comp (GUf E n).subtype).codRestrict _ fun g => invT_mem_Sim g.2

def th0 : Gam0 E n →* Gam0 E n :=
  (((invT n E).prodMap invMonoidHom).comp (Gam0 E n).subtype).codRestrict _ fun g =>
    ⟨invT_mem_Sim g.2.1, (Units.posSubgroup ℚ).inv_mem g.2.2⟩

@[simp] theorem sim_th (g : GUf E n) : sim (th g) = (sim g)⁻¹ := rfl

@[simp] theorem mat_th (g : GUf E n) : mat (th g) = invT n _ (mat g) := rfl

@[simp] theorem comp_th (w : Plc E) (g : GUf E n) : comp w (th g) = invT n _ (comp w g) := GlobalTheory.SplitPts.invT_map _ _

@[simp] theorem th_th (g : GUf E n) : th (th g) = g := Subtype.ext (Prod.ext (invT_invT' _) (inv_inv _))

theorem th_rat (γ : Gam0 E n) : th (rat γ) = rat (th0 γ) :=
  Subtype.ext (Prod.ext (GlobalTheory.SplitPts.invT_map _ _).symm (map_inv (Units.map (algebraMap ℚ AfQ).toMonoidHom) _).symm)

theorem guf_ext {g g' : GUf E n} (h1 : sim g = sim g') (h2 : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun w => congrArg Units.val (h2 w))) h1)

theorem invT_mem_KGL {w : Plc E} {y : GLw n w} (h : y ∈ KGL w n) : invT n _ y ∈ KGL w n := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨invT n _ z, GlobalTheory.SplitPts.invT_map _ z⟩

def levT (Kw : ∀ w : Plc E, Subgroup (GLw n w)) : ∀ w : Plc E, Subgroup (GLw n w) := fun w => (Kw w).comap (invT n _)

theorem th_mem_lev {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {k : GUf E n} :
    th k ∈ lev S Kw ↔ k ∈ lev S (levT Kw) := by
  simp only [mem_lev, sim_th, comp_th, inv_mem_iff, levT, Subgroup.mem_comap]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₃_congr fun w _ _ => ⟨fun h => ?_, invT_mem_KGL⟩
  simpa using invT_mem_KGL h

def embBar (E : Type) [Field E] (n : ℕ) : GL (Fin n) E →* (InfinitePlace E → GL (Fin n) ℂ) :=
  MonoidHom.pi fun v => GeneralLinearGroup.map (ComplexEmbedding.conjugate v.embedding)

def xiG (W : Wt E n) (c : InfinitePlace E → ℤ) : Representation ℂ (GL (Fin n) E × ℚˣ) (Module.Dual ℂ W.Sp) where
  toFun p := (∏ v : InfinitePlace E, (v.embedding p.1.val.det * ComplexEmbedding.conjugate v.embedding p.1.val.det) ^ (-c v)) •
    Representation.dual ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embBar E n)) p.1
  map_one' := by
    rw [Prod.fst_one, map_one (Representation.dual _)]
    simp
  map_mul' p q := by
    rw [Prod.fst_mul, map_mul (Representation.dual _), smul_mul_smul_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Units.val_mul, det_mul, map_mul, map_mul, ← mul_zpow, mul_mul_mul_comm]

def jOf (W : Wt E n) (c : InfinitePlace E → ℤ) : ℤ := ∑ v, ((∑ i, (W v).w i) + n * c v)

structure IsFormG (x : E) (U : Submodule ℂ (UA E n → ℂ)) (W : Wt E n) (c : InfinitePlace E → ℤ) (w₀ : Plc E) (J : Subgroup (GLw n w₀)) (χ : J →* ℂˣ)
    (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (Φ : GUf E n → Module.Dual ℂ W.Sp) (κ : HChar E) : Prop where
  ne : Φ ≠ 0
  left : ∀ (γ : Gam0 E n) g, Φ (rat γ * g) = xiG W c γ.1 (Φ g)
  right : ∀ k ∈ lev S Kw, ∀ h : invT n _ (comp w₀ k) ∈ J, ∀ g, Φ (g * k) = ((χ ⟨_, h⟩ : ℂˣ) : ℂ) • Φ g
  sat : ∀ (w : Plc E) (hw : IsSplitAt w), w ∉ S → cj w ∉ S → ∀ B, SatU U w B →
    IsSatVecGL w (((rightReg ℂ (GUf E n) (Module.Dual ℂ W.Sp)).comp (loc hw)).comp (invT n _)) Φ B
  alg : IsAlgPos κ (mOf x W (jOf W c))
  unr : ∀ w : Plc E, (∀ u ∈ S, ¬ SameK x (cj u) w) → κ.UnrAt w
  cen : ∀ w : Plc E, (∀ u ∈ S, ¬ SameK x (cj u) w) → ¬ SameK x (cj w) w → ∀ z, IsCen x w z →
    ∀ g, Φ (g * z⁻¹) = ((κ.val w : ℂˣ) : ℂ)⁻¹ • Φ g

def SeedG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (π : AutSub E n) (W : Wt E n), π.finPart W ≠ ⊥ → ∀ (c : InfinitePlace E → ℤ) (Up : Plc E → Prop), (∀ w, IsSplitAt w → Up w ∨ Up (cj w)) →
  ∀ w₀ : Plc E, IsSplitAt w₀ → Up w₀ → ∀ (J : Subgroup (GLw n w₀)) (χ : J →* ℂˣ), IsOpen (J : Set (GLw n w₀)) →
    IsCompact (J : Set (GLw n w₀)) → HasType π.V w₀ J χ →
  ∃ (S : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (Φ : GUf E n → Module.Dual ℂ W.Sp) (κ : HChar E),
    Shape Up w₀ S Kw ∧ Kw w₀ = J.comap (invT n _) ∧ IsOpen {k : J | χ k = 1} ∧ IsOpen (lev S Kw : Set (GUf E n)) ∧
    IsCompact (lev S Kw : Set (GUf E n)) ∧
    (∀ w, IsSplitAt w → Apart w w₀ → (∃ B, SatU π.V w B) → w ∉ S ∧ cj w ∉ S) ∧ IsFormG x π.V W c w₀ J χ S Kw Φ κ

def XiTh : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (c : InfinitePlace E → ℤ) (γ : Gam0 E n),
  xi0 W (jOf W c) (th0 γ) = xiG W c γ.1

def ThLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ (w : Plc E) (hw : IsSplitAt w) (y : GLw n w), th (loc hw y) = loc hw (invT n _ y)) ∧
    (0 < n → ∀ (x : E) (w : Plc E) (z : GUf E n), IsCen x w z → th z = z⁻¹)

theorem seedG_of (h0 : SeedGU) (h1 : XiTh) (h2 : ThLoc) (h3 : LevOpen) (h4 : LevCompact) : SeedG := by
  intro E _ _ _ n hn d x hd hx π W hW c Up hUp w₀ hw₀ hu J χ hJo hJc hT
  obtain ⟨S, Kw, Φ, κ, hS, hJ, hχ, -, -, hsph, hΦ, hκ⟩ := h0 E n hn d x hd hx π W hW (jOf W c) Up hUp w₀ hw₀ hu J χ hJo hJc hT
  have hS' : Shape Up w₀ S (levT Kw) := by
    refine ⟨hS.mem, fun w hw => (hS.opn w hw).preimage (GlobalTheory.SplitPts.continuous_invT _), fun w hw => ?_, fun w hw hne y hy => ?_, hS.up⟩
    · convert (hS.cpt w hw).image (GlobalTheory.SplitPts.continuous_invT (n := n) _) using 1
      ext y
      exact ⟨fun h => ⟨_, h, invT_invT' y⟩, fun ⟨z, hz, e⟩ => e ▸ (show invT n _ (invT n _ z) ∈ Kw w by rwa [invT_invT'])⟩
    · simpa using invT_mem_KGL (hS.le w hw hne hy)
  refine ⟨S, levT Kw, fun g => Φ (th g), κ, hS', by rw [levT, hJ], hχ, h3 E n S _ hS'.opn, h4 E n Up w₀ hw₀ S _ hS', hsph,
    fun h => hΦ.ne (funext fun g => by simpa using congrFun h (th g)), fun γ g => ?_, fun k hk h g => ?_, fun w hw a b B hB => ?_,
    hκ.alg, hκ.unr, fun w a b z hz g => ?_⟩
  · rw [map_mul, th_rat, hΦ.left, h1]
  · have h' : comp w₀ (th k) ∈ J := by rwa [comp_th]
    rw [map_mul, hΦ.right _ (th_mem_lev.2 hk) h']
    congr 3
  · obtain ⟨s1, s2, s3, s4⟩ := hΦ.sat w hw a b B hB
    let L : (GUf E n → Module.Dual ℂ W.Sp) ≃ₗ[ℂ] (GUf E n → Module.Dual ℂ W.Sp) :=
      LinearEquiv.funCongrLeft ℂ _ ⟨th, th, th_th, th_th⟩
    have hL : ∀ y Ψ, L (((rightReg ℂ (GUf E n) (Module.Dual ℂ W.Sp)).comp (loc hw)) y Ψ) =
        (((rightReg ℂ (GUf E n) (Module.Dual ℂ W.Sp)).comp (loc hw)).comp (invT n _)) y (L Ψ) := fun y Ψ => funext fun g => by
      show Ψ (th g * loc hw y) = Ψ (th (g * loc hw (invT n _ y)))
      rw [map_mul, (h2 E n).1, invT_invT']
    refine ⟨fun h => s1 (L.map_eq_zero_iff.1 h), GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, s3, fun p hp i hi => ?_⟩
    · exact (hL k Φ).symm.trans (congrArg L (GlobalTheory.LGrp.mem_fixed.1 s2 k hk))
    · have e := congrArg L (s4 p hp i hi)
      rw [map_smul] at e
      refine Eq.trans ?_ e
      unfold heckeVec
      rw [show L (∑ᶠ c, _) = _ from L.toAddEquiv.map_finsum _]
      refine finsum_congr fun c => ?_
      exact ((congrArg _ (hL _ Φ)).symm.trans (L.map_smul _ _).symm)
  · rw [map_mul, map_inv, (h2 E n).2 hn x w z hz, inv_inv, hκ.cen w a b z hz]

end UpperTheory.Gal.CertificateRingHomMap

end
