import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedPullConstMorVPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTGlueLie
variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem inr_one_mul (y : TrivSqZeroExt k k) :
    (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * y = TrivSqZeroExt.inr y.fst := by
  ext
  · simp
  · simp

theorem fstC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    fstC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) = 0 := by
  ext c
  rw [fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).fst = 0
  rw [inr_one_mul, TrivSqZeroExt.fst_inr]

theorem sndC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    (sndC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) : HdR A₀) = fstC A₀ e := by
  ext c
  change (sndC A₀ _) c = fstC A₀ e c
  rw [sndC_apply, fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).snd = _
  rw [inr_one_mul, TrivSqZeroExt.snd_inr]

theorem exists_of_coords_self (hA : IsAbelianScheme A₀) (x : HdR A₀) (y : primDR A₀ →ₗ[k] k) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, fstC A₀ e = x ∧ sndC A₀ e = y :=
  exists_of_coords hA x y

theorem ext_coords_self (hA : IsAbelianScheme A₀) {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀}
    (h1 : fstC A₀ e = fstC A₀ e') (h2 : (sndC A₀ e : HdR A₀) = sndC A₀ e') : e = e' :=
  ext_coords hA h1 h2

set_option maxHeartbeats 1600000 in

theorem dualNumber_hodge_summand_eq_graph_coords_of_compl (hA : IsAbelianScheme A₀) (f : HdR A₀ →ₗ[k] HdR A₀)
    (E M : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hEM : IsCompl E M)
    (h2 : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y)
    (h3 : ∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀) := by
  have hε := fun e' ↦ And.intro (fstC_inr_smul (A₀ := A₀) e') (sndC_inr_smul (A₀ := A₀) e')
  have hc : ∀ x ∈ Fil A₀, ∃ e ∈ E, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f x := by
    intro x hx
    refine (h3 x hx).elim fun e₁ hh ↦ ⟨e₁, hh.1, ?_, ?_⟩
    · ext c; rw [fstC_apply, hh.2 c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · ext c; show (sndC A₀ e₁) c = _; rw [sndC_apply, hh.2 c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  have hfil : ∀ a ∈ E, fstC A₀ a ∈ Fil A₀ := fun a ha ↦ (h2 _).2 ⟨a, ha, (corr_iff_fstC hA a _).2 rfl⟩
  constructor
  · intro he
    have hx := hfil e he
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    refine ⟨hx, ?_⟩
    have hh := exists_of_coords_self hA ((sndC A₀ e : HdR A₀) - f (fstC A₀ e)) 0
    obtain ⟨yh, hy1, -⟩ := hh
    have hεy : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh = e - e₁ := by
      refine ext_coords_self hA ?_ ?_
      · rw [(hε yh).1, map_sub, h1, sub_self]
      · have h5 := (hε yh).2
        rw [hy1] at h5
        show (sndC A₀ _ : HdR A₀) = sndC A₀ (e - e₁)
        rw [h5, map_sub]
        show _ = (sndC A₀ e : HdR A₀) - (sndC A₀ e₁ : HdR A₀)
        rw [h1']
    have hmem : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh ∈ E := hεy ▸ E.sub_mem he he₁
    have hyt : yh ∈ E ⊔ M := hEM.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, m, hm, hsum⟩ := Submodule.mem_sup.1 hyt
    have hεm : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m ∈ E := by
      have := E.sub_mem hmem (E.smul_mem (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) ha)
      rwa [← hsum, smul_add, add_sub_cancel_left] at this
    have hm0 : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m = 0 :=
      (Submodule.disjoint_def.1 hEM.disjoint) _ hεm (M.smul_mem _ hm)
    have hm1 : fstC A₀ m = 0 := by rw [← (hε m).2, hm0, map_zero]
    rw [← hy1, ← hsum, map_add, hm1, add_zero]
    exact hfil a ha
  · rintro ⟨hx, hz⟩
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    obtain ⟨e₂, he₂, h2a, -⟩ := hc _ hz
    have : e = e₁ + (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e₂ := by
      refine ext_coords_self hA ?_ ?_
      · rw [map_add, (hε e₂).1, h1, add_zero]
      · show (sndC A₀ e : HdR A₀) = (sndC A₀ (e₁ + _) : HdR A₀)
        rw [map_add]
        show _ = (sndC A₀ e₁ : HdR A₀) + (sndC A₀ (_ • e₂) : HdR A₀)
        rw [(hε e₂).2, h1', h2a, add_sub_cancel]
    rw [this]
    exact E.add_mem he₁ (E.smul_mem _ he₂)

theorem fo_summand_coords : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)), (∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀), IsCompl E M) → (∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y) → (∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c)) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, e ∈ E ↔ (GlobalTheory.HTGlueLie.fstC A₀ e ∈ Fil A₀ ∧ (GlobalTheory.HTGlueLie.sndC A₀ e : HdR A₀) - f (GlobalTheory.HTGlueLie.fstC A₀ e) ∈ Fil A₀) := fun _ _ _ _ hA f E ⟨M, hEM⟩ h2 h3 e ↦
  dualNumber_hodge_summand_eq_graph_coords_of_compl hA f E M hEM h2 h3 e

end GlobalTheory.HTGlueLie
