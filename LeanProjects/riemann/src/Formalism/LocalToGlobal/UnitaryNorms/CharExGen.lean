import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

variable (L : Type) [Field L] [NumberField L]

def unitIdeles : Subgroup (Ideles L) where
  carrier := {u | ∀ v : HeightOneSpectrum (𝓞 L), Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1}
  one_mem' := fun v => by rw [comp_one]; exact map_one _
  mul_mem' := fun {a b} ha hb v => by
    show Valued.v (((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v) = 1
    rw [comp_mul, map_mul, ha v, hb v, one_mul]
  inv_mem' := fun {a} ha v => by
    have h := congrArg Valued.v (comp_mul_inv L a v)
    rw [map_mul, ha v, one_mul, map_one] at h
    exact h

theorem mem_unitIdeles_iff (u : Ideles L) : u ∈ unitIdeles L ↔ u ∈ rayUnits L ⊤ ∅ := by
  rw [rayUnits_top_iff]
  exact Iff.rfl

def OpenUnits : Prop := IsOpen (unitIdeles L : Set (Ideles L))

def DivExtC : Prop :=
  ∀ (G : Type) [CommGroup G] (H : Subgroup G) (g : H →* ℂˣ), ∃ g' : G →* ℂˣ, ∀ x : H, g' x = g x

def ClassExp : Prop := ∃ h : ℕ, 0 < h ∧ ∀ x : Ideles L, ∃ k : Lˣ, x ^ h * diagUnits L k ∈ unitIdeles L

theorem classExp : ClassExp L := by
  refine ⟨Fintype.card (ClassGroup (𝓞 L)), Fintype.card_pos, fun x => ?_⟩
  have h1 : classOf L (x ^ Fintype.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, u, hu, hx⟩ := (classOf_eq_one_iff L _).mp h1
  refine ⟨k⁻¹, ?_⟩
  rw [hx, map_inv, mul_comm (diagUnits L k) u, mul_inv_cancel_right]
  exact (mem_unitIdeles_iff L u).mpr hu

variable {L}

theorem exists_hchar_eq_on (hD : DivExtC) (hO : OpenUnits L) (M : Subgroup (Ideles L)) (hM : unitIdeles L ≤ M)
    (Φ : Ideles L →* ℂˣ) (hΦ : Continuous Φ) (h1 : ∀ k : Lˣ, diagUnits L k ∈ M → Φ (diagUnits L k) = 1) :
    ∃ χ : HChar L, ∀ m ∈ M, χ.1 m = Φ m := by
  set D : Subgroup (Ideles L) := (diagUnits L).range
  let K0 : Subgroup M := D.comap M.subtype
  have hK : K0 ≤ (Φ.comp M.subtype).ker := by
    intro x hx
    have hx' : (x : Ideles L) ∈ (diagUnits L).range := hx
    obtain ⟨k, hk⟩ := hx'
    have hkM : diagUnits L k ∈ M := hk ▸ x.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hk]
    exact h1 k hkM
  let φ1 : M ⧸ K0 →* ℂˣ := QuotientGroup.lift K0 (Φ.comp M.subtype) hK
  let ι : M ⧸ K0 →* Ideles L ⧸ D := QuotientGroup.map K0 D M.subtype le_rfl
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_one ι).mpr fun a ha => ?_
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at ha
      exact (QuotientGroup.eq_one_iff x).mpr ha
  let e : M ⧸ K0 ≃* ι.range := MonoidHom.ofInjective hι
  let g : ι.range →* ℂˣ := φ1.comp e.symm.toMonoidHom
  obtain ⟨g', hg'⟩ := hD (Ideles L ⧸ D) ι.range g
  let χ0 : Ideles L →* ℂˣ := g'.comp (QuotientGroup.mk' D)
  have hχM : ∀ m ∈ M, χ0 m = Φ m := by
    intro m hm
    have hq : ((e (QuotientGroup.mk ⟨m, hm⟩) : ι.range) : Ideles L ⧸ D) = (m : Ideles L ⧸ D) := by
      rw [MonoidHom.ofInjective_apply]
      rfl
    have h2 := hg' (e (QuotientGroup.mk ⟨m, hm⟩))
    rw [hq] at h2
    change g' (m : Ideles L ⧸ D) = Φ m
    rw [h2]
    simp [g, φ1]
  have hcont : Continuous χ0 := by
    refine continuous_of_continuousAt_one χ0 ?_
    have hev : Φ =ᶠ[nhds 1] χ0 := by
      filter_upwards [hO.mem_nhds (unitIdeles L).one_mem] with x hx
      exact (hχM x (hM hx)).symm
    exact hΦ.continuousAt.congr hev
  have hdiag : ∀ k : Lˣ, χ0 (diagUnits L k) = 1 := by
    intro k
    have hmem : diagUnits L k ∈ D := ⟨k, rfl⟩
    change g' (QuotientGroup.mk' D (diagUnits L k)) = 1
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hmem, map_one]
  exact ⟨⟨χ0, hcont, hdiag⟩, hχM⟩

theorem norm_pow_eq_one {z : ℂˣ} {h : ℕ} (hh : 0 < h) (hz : ‖((z ^ h : ℂˣ) : ℂ)‖ = 1) : ‖(z : ℂ)‖ = 1 := by
  rw [Units.val_pow_eq_pow_val, norm_pow] at hz
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').mp hz

theorem isUnitary_of_unitIdeles (χ : HChar L) (h : ∀ u ∈ unitIdeles L, ‖((χ.1 u : ℂˣ) : ℂ)‖ = 1) : χ.IsUnitary := by
  obtain ⟨n, hn, hx⟩ := classExp L
  intro x
  obtain ⟨k, hk⟩ := hx x
  apply norm_pow_eq_one hn
  have h2 := h _ hk
  rwa [map_mul, χ.2.2 k, mul_one, map_pow] at h2

end CharEx

end Formalism.L2.Host
