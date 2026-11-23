import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rop_single {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (u : H) (Φ : H → V) (g : H) :
    rop (Finsupp.single u 1) Φ g = Φ (g * u) := by
  unfold rop
  rw [Finsupp.sum_single_index (by simp), one_smul]

private theorem rop_sum {H V Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] (R : Finset Y) (e : Y → H) (Φ : H → V) (g : H) :
    rop (∑ y ∈ R, Finsupp.single (e y) 1) Φ g = ∑ y ∈ R, Φ (g * e y) := by
  unfold rop
  rw [← Finsupp.sum_finset_sum_index (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun y _ => by rw [Finsupp.sum_single_index (by simp), one_smul]

private structure HI {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (U : Submodule ℂ (UA E n → ℂ)) (S : Finset (Plc E)) where
  w : Plc E
  hw : IsSplitAt w
  h1 : w ∉ S
  h2 : cj w ∉ S
  B : Multiset ℂˣ
  hB : SatU U w B
  p : w.adicCompletion E
  hp : Formalism.UG.IsUnifV E w p
  i : ℕ
  hi : i ≤ n

set_option maxHeartbeats 1600000 in
theorem pFormGU_of (hExt : ExtEig2) (hCl : ClassFin) (hXi : XiZeta) (hKer : KerFormU) (hHk : HeckePres) (hSat : SatVal)
    (hMem : LocMem) (hComm : LocComm) (hOp : LevOpen) (hU : OfUBij) : FormGU := by
  intro E _ _ _ n x ζ hζ π W j Up w₀ hw₀ S Kw hS χ hχ f hf hf0 hfix
  obtain ⟨-, hap, -, -, hcc, -⟩ := hComm E n w₀ hw₀
  have hc0 : cj w₀ ∉ S := (hS.up w₀ hS.mem hw₀).2
  let Kw' := Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)
  have mem' : ∀ k : GUf E n, k ∈ lev S Kw' ↔ k ∈ lev S Kw ∧ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
    intro k
    have e0 : comp w₀ k ∈ Kw' w₀ ↔ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
      simp only [Kw', Function.update_self, Subgroup.mem_map, MonoidHom.mem_ker]
      exact ⟨fun ⟨y, hy, e⟩ => ⟨e ▸ y.2, by rw [← hy]; congr 1; exact Subtype.ext e.symm⟩, fun ⟨h, e⟩ => ⟨⟨_, h⟩, e, rfl⟩⟩
    have e1 : ∀ w, w ≠ w₀ → Kw' w = Kw w := fun w hw => Function.update_of_ne hw _ _
    rw [mem_lev, mem_lev]
    constructor
    · rintro ⟨a, b, c⟩
      obtain ⟨h, hh⟩ := e0.1 (b _ hS.mem)
      refine ⟨⟨a, fun w hw => ?_, c⟩, h, hh⟩
      by_cases e : w = w₀
      · subst e; exact h
      · rw [← e1 w e]; exact b w hw
    · rintro ⟨⟨a, b, c⟩, h⟩
      refine ⟨a, fun w hw => ?_, c⟩
      by_cases e : w = w₀
      · subst e; exact e0.2 h
      · rw [e1 w e]; exact b w hw
  have hopen : IsOpen (lev S Kw' : Set (GUf E n)) := by
    refine hOp E n S Kw' fun w hw => ?_
    by_cases e : w = w₀
    · subst e
      simp only [Kw', Function.update_self]
      exact (hS.opn w hw).isOpenMap_subtype_val _ hχ
    · simp only [Kw', Function.update_of_ne e]; exact hS.opn w hw
  have hfix' : ∀ u : finU E n, ofU u ∈ lev S Kw' → algRep W u f = f := fun u hu => by
    obtain ⟨a, h, e⟩ := (mem' _).1 hu
    have := hfix u a h
    rwa [show χ ⟨cLoc w₀ u.1, h⟩ = 1 from e, Units.val_one, one_smul] at this
  obtain ⟨φ, hφ, hφu, hφ0⟩ := hKer E n W j f hf0 (lev S Kw') (fun k hk => (mem_lev.1 hk).1) hfix'
  have hloc : ∀ y : Kw w₀, loc hw₀ y.1 ∈ lev S Kw := fun y => (hMem E n S Kw w₀ hw₀ hc0 y.1).1 hS.mem y.2
  choose R hR1 hR2 using fun a : HI π.V S => hHk E n a.w a.hw a.p a.hp a.i
  have hsv : ∀ (w : Plc E) (hw : IsSplitAt w), w ∉ S → cj w ∉ S → ∀ B, SatU π.V w B →
      IsSatVecGL w ((algRep W).comp (locF hw)) f B := fun w hw h1 h2 B hB =>
    hSat E n π W f hf hf0 w hw (fun k hk => hfix' _ ((hMem E n S Kw' w hw h2 k).2 h1 hk)) B hB
  obtain ⟨Φ, hΦ, hΦ0, heig, ψ, hψ⟩ := hExt (Gam0 E n) (GUf E n) AfQˣ (Af E)ˣ _ rat (lev S Kw') (xi0 W j) sim ζ hζ.central
    (by
      obtain ⟨s, hs⟩ := hCl E ((lev S Kw').comap ζ) (hopen.preimage hζ.cont)
      refine ⟨s, fun z => ?_⟩
      obtain ⟨t, ht, o, ho, k, e⟩ := hs z
      obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
      exact ⟨t, ht, o, _, e, ho, γ, _, h1, h2⟩)
    φ hφ hφ0 (Kw w₀ ⊕ HI π.V S)
    (Sum.elim (fun y => Finsupp.single (loc hw₀ y.1) 1) fun a => ∑ y ∈ R a, Finsupp.single (loc a.hw y) 1)
    (Sum.elim (fun y => (χ y : ℂ)) fun a => satEig (Formalism.UG.qV E a.w) n a.B a.i)
    (by
      rintro (y | a) u hu
      · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hu)
        rfl
      · obtain ⟨y, -, hy⟩ := Finsupp.mem_support_finset_sum u hu
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hy)
        rfl)
    (by
      rintro (y | a) Ψ hΨ
      · refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
        · simp only [Sum.elim_inl, rop_single, mul_assoc, hΨ.1]
        · simp only [Sum.elim_inl, rop_single]
          obtain ⟨a, h, e⟩ := (mem' _).1 hk
          have hk' : (loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1 ∈ lev S Kw' := by
            have h' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) = (y⁻¹ * ⟨_, h⟩ * y : Kw w₀) := by
              rw [map_mul, map_mul, map_inv, comp_loc]; rfl
            have h'' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) ∈ Kw w₀ := by rw [h']; exact Subtype.property _
            refine (mem' _).2 ⟨mul_mem (mul_mem (inv_mem (hloc y)) a) (hloc y), h'', ?_⟩
            rw [show (⟨_, h''⟩ : Kw w₀) = y⁻¹ * ⟨_, h⟩ * y from Subtype.ext h', map_mul, map_mul, e, map_inv, mul_one,
              inv_mul_cancel]
          rw [← hΨ.2 _ hk' (g * loc hw₀ y.1)]
          simp only [mul_assoc, mul_inv_cancel_left]
      · have := hR2 a S Kw' a.h1 a.h2 _ (xi0 W j) Ψ hΨ
        convert this using 1
        funext g
        exact rop_sum _ _ _ _)
    (by
      rintro (y | a) g hg
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inl, rop_single]
        have h : cLoc w₀ (locF hw₀ y.1).1 ∈ Kw w₀ := by rw [cLoc_locF]; exact y.2
        have e := hfix (locF hw₀ y.1) (hloc y) h
        rw [show (⟨_, h⟩ : Kw w₀) = y from Subtype.ext (cLoc_locF _ _)] at e
        rw [show ofU u * loc hw₀ y.1 = ofU (u * locF hw₀ y.1) from (map_mul ofU _ _).symm, hφu, hφu]
        rw [Subgroup.coe_mul, ← algForms.val_algRep, e]
        rfl
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inr, rop_sum]
        have e := (hsv a.w a.hw a.h1 a.h2 a.B a.hB).2.2.2 a.p a.hp a.i a.hi
        rw [hR1 a] at e
        have e2 : ∀ y, φ (ofU u * loc a.hw y) = algForms.val (((algRep W).comp (locF a.hw)) y f) u.1 := fun y => by
          rw [show ofU u * loc a.hw y = ofU (u * locF a.hw y) from (map_mul ofU _ _).symm, hφu]
          rfl
        simp only [e2]
        let L : algForms W →ₗ[ℂ] Module.Dual ℂ W.Sp :=
          { toFun := fun F => algForms.val F u.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        have e3 := congrArg L e
        rw [map_sum, map_smul] at e3
        rw [hφu]
        exact e3)
  refine ⟨Φ, ψ, ⟨hΦ0, hΦ.1, fun k hk h g => ?_, fun w hw h1 h2 B hB => ⟨hΦ0, ?_, (hsv w hw h1 h2 B hB).2.2.1, fun p hp i hi => ?_⟩⟩, hψ.1⟩
  · have h1 := congrFun (heig (Sum.inl ⟨_, h⟩)) g
    simp only [Sum.elim_inl, rop_single, Pi.smul_apply] at h1
    have h' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) = 1 := by rw [map_mul, map_inv, comp_loc, inv_mul_cancel]
    have h'' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) ∈ Kw w₀ := by rw [h']; exact one_mem _
    have hk' : (loc hw₀ (comp w₀ k))⁻¹ * k ∈ lev S Kw' :=
      (mem' _).2 ⟨mul_mem (inv_mem (hloc ⟨_, h⟩)) hk, h'', by
        rw [show (⟨_, h''⟩ : Kw w₀) = 1 from Subtype.ext h', map_one]⟩
    rw [← h1, ← hΦ.2 _ hk' (g * loc hw₀ (comp w₀ k)), mul_assoc, mul_inv_cancel_left]
  · exact GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext fun g => hΦ.2 _ ((hMem E n S Kw' w hw h2 k).2 h1 hk) g
  · let a : HI π.V S := ⟨w, hw, h1, h2, B, hB, p, hp, i, hi⟩
    have h3 := heig (Sum.inr a)
    rw [show heckeVec _ _ _ Φ = _ from hR1 a _ _ Φ]
    refine Eq.trans ?_ h3
    funext g
    rw [Finset.sum_apply]
    exact (rop_sum _ _ _ _).symm

end UpperTheory.Gal.CertificateRingHomMap
