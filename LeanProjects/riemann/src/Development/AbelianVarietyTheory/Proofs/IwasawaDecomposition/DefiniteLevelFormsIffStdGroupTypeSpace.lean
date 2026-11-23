import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRationalGLOfUnitaryGroupGramUnitGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelSubgroupBoundedOpenHyperspecialStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.MtInType

variable {D : D7}

theorem km_eq {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    Formalism.UG.bc (swapAE D) ((toGf P g : Bridge.Gf V) : GL _ _) = km D V.rank g := hU g

section Mem

variable {V : HSp D} (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)

theorem rowFrameImage_mem_levelQ_iff_swap {P : principalLevelFrame.RowPsi V V.rank} (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q ↔
      Formalism.UG.bc (swapAE D) ((toGf P g : Bridge.Gf V) : GL _ _) ∈ lev D.sp.cm V.gram 1
        (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) := by
  unfold levEnv
  rw [Subgroup.mem_comap]
  rfl

theorem mem_Q_iff (hg : V.gram = 1) {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q ↔
      km D V.rank g ∈ parLev D.sp.cm (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) 1
        (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) := by
  rw [rowFrameImage_mem_levelQ_iff_swap, km_eq P hU, hg, mem_lev]
  exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top _⟩⟩

theorem mem_stdFrameLevelSubgroup_iff_parabolicLevel (LP : LevelP Pg D.R.r ℂ) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    g ∈ stdJ (datV D V.rank hr Pg Q LP chi xi) ↔
      km D V.rank g ∈ parLev D.sp.cm (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) 1
        (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) ∧
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g) ∈ LP.H := by
  unfold stdJ
  rw [Subgroup.mem_comap, mem_lev]
  rfl

variable {G₀ : Type} [Group G₀]

theorem mem_levPOf_H {K : Type} [Field K] (eG : G₀ ≃* G0 Pg D.R.r) (σ : K →+* ℂ) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* Kˣ) (x : G₀) :
    eG x ∈ (levPOf eG σ P₀ ψ₀).H ↔ x ∈ P₀ := by
  show eG.symm.toMonoidHom (eG x) ∈ P₀ ↔ _
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem red_eq {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P)
    (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (g : Formalism.AUTREP.GAf D.host.E V.rank) (h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q) :
    eG (red ⟨_, h⟩) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g) :=
  (hred ⟨_, h⟩).trans (congrArg (rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) (km_eq P hU g))

theorem mem_stdJ_iff (hg : V.gram = 1) {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P)
    (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    g ∈ stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi) ↔
      ∃ h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, red ⟨_, h⟩ ∈ P₀ := by
  have hQ := mem_Q_iff hr Pg Q chi xi hg hU (P := P) g
  have hH : ∀ h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q,
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g) ∈ (levPOf eG D.what₂.embLL P₀ ψ₀).H ↔
        red ⟨_, h⟩ ∈ P₀ := by
    intro h
    rw [← red_eq hr Pg Q chi xi hU red eG hred g h]
    exact mem_levPOf_H Pg eG D.what₂.embLL P₀ ψ₀ _
  refine (mem_stdFrameLevelSubgroup_iff_parabolicLevel hr Pg Q chi xi _ g).trans ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hQ.2 h1, (hH (hQ.2 h1)).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hQ.1 h1, (hH h1).2 h2⟩

end Mem

section Chr

variable {V : HSp D} (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
variable {G₀ : Type} [Group G₀]

theorem levPOf_ext1_apply_eq_units_map_inv {K : Type} [Field K] (eG : G₀ ≃* G0 Pg D.R.r) (σ : K →+* ℂ) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* Kˣ)
    (x : G₀) (hx : x ∈ P₀) :
    ext1 (levPOf eG σ P₀ ψ₀).conj.H (levPOf eG σ P₀ ψ₀).conj.chi (eG x) = Units.map σ.toMonoidHom ((ψ₀ ⟨x, hx⟩)⁻¹) := by
  rw [extendOne_of_mem _ (show eG x ∈ (levPOf eG σ P₀ ψ₀).conj.H from (mem_levPOf_H Pg eG σ P₀ ψ₀ x).2 hx)]
  show ((Units.map σ.toMonoidHom) (ψ₀ ((eG.symm.toMonoidHom.subgroupComap P₀) ⟨eG x, _⟩)))⁻¹ = _
  have e : (eG.symm.toMonoidHom.subgroupComap P₀) ⟨eG x, (mem_levPOf_H Pg eG σ P₀ ψ₀ x).2 hx⟩ = ⟨x, hx⟩ :=
    Subtype.ext (eG.symm_apply_apply x)
  rw [e, map_inv]

theorem extension_conj_character_eq {K : Type} [Field K] (eG : G₀ ≃* G0 Pg D.R.r) (σ : K →+* ℂ) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* Kˣ)
    (x : G₀) (hx : x ∈ P₀) (y : G0 Pg D.R.r) (hy : eG x = y) :
    ext1 (levPOf eG σ P₀ ψ₀).conj.H (levPOf eG σ P₀ ψ₀).conj.chi y = ((Units.map σ.toMonoidHom).comp ψ₀⁻¹) ⟨x, hx⟩ := by
  subst hy
  rw [levPOf_ext1_apply_eq_units_map_inv Pg eG σ P₀ ψ₀ x hx]
  rfl

theorem stdX_eq (hg : V.gram = 1) {P : principalLevelFrame.RowPsi V V.rank} (hU : UnitFr P)
    (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (g : Formalism.AUTREP.GAf D.host.E V.rank) (hJ : g ∈ stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi))
    (h : toGf P g ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q) (hP : red ⟨_, h⟩ ∈ P₀) :
    stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi) ⟨g, hJ⟩ =
      (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch ⟨_, h⟩ *
        ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red ⟨_, h⟩, hP⟩ := by
  have e1 : stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi) ⟨g, hJ⟩ =
      ext1 (levPOf eG D.what₂.embLL P₀ ψ₀).conj.H (levPOf eG D.what₂.embLL P₀ ψ₀).conj.chi
        (rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g)) *
      levFn 1 (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) (km D V.rank g) :=
    levFn_withP (V := V) (L := datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) _ _
  have e2 : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch ⟨_, h⟩ =
      levFn 1 (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) (km D V.rank g) :=
    congrArg (levFn 1 (flagL (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi))) (km_eq P hU g)
  have e3 : ext1 (levPOf eG D.what₂.embLL P₀ ψ₀).conj.H (levPOf eG D.what₂.embLL P₀ ψ₀).conj.chi
        (rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (km D V.rank g)) =
      ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red ⟨_, h⟩, hP⟩ := by
    exact extension_conj_character_eq Pg eG D.what₂.embLL P₀ ψ₀ _ hP _ (red_eq hr Pg Q chi xi hU red eG hred g h)
  exact e1.trans ((mul_comm _ _).trans (congrArg₂ (· * ·) e2.symm e3))

end Chr

section Jlev

variable {V : HSp D} (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
variable {G₀ : Type} [Group G₀]

theorem mem_twoBlockLevelJ_iff_swap (k : Bridge.Gf V) :
    k ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J ↔
      Formalism.UG.bc (swapAE D) (k : GL _ _) ∈ lev D.sp.cm V.gram 1
        (flag1L (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)) := by
  unfold levEnv
  rw [Subgroup.mem_comap]
  rfl

theorem red_J (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r)
    (hred : ∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    (k : Bridge.Gf V) (hk : k ∈ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J) :
    red ⟨k, (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J_le hk⟩ = 1 := by
  apply eG.injective
  rw [map_one, hred]
  have h2 := ((mem_twoBlockLevelJ_iff_swap hr Pg Q chi xi k).1 hk).2
  exact Subgroup.mem_bot.1 h2

end Jlev

section Main

variable {V : HSp D} {hr : D.R.r ≤ V.rank} {Pg Q : Finset (Pl D.host.E)} {chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
  {c : CoefA V} {P : principalLevelFrame.RowPsi V V.rank} {e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V}
  {G₀ : Type} [Group G₀] {eG : G₀ ≃* G0 Pg D.R.r} {P₀ : Subgroup G₀} {ψ₀ : P₀ →* D.what₂.LLˣ}

local notation "LE" => levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)
local notation "LP" => datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi

theorem fwd_rat (hR : RatIso P e) {F : Bridge.Gf V → c.W} (hA : F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (LE).J (LE).χ)
    (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    F (toGf P (↑γ * g)) = c.coef.ρ (e γ) (F (toGf P g)) := by
  have h1 := hA (e γ) (toGf P g) 1
  simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at h1
  rw [(hR γ).1, ← map_mul] at h1
  exact h1

set_option maxHeartbeats 4000000 in
theorem bwd_ad (hg : V.gram = 1) (hU : UnitFr P) (hR : RatIso P e)
    (red : (LE).Q →* G₀)
    (hred : ∀ q : (LE).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    {F : Bridge.Gf V → c.W}
    (hAut : ∀ (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) (g : Formalism.AUTREP.GAf D.host.E V.rank),
      F (toGf P (↑γ * g)) = c.coef.ρ (e γ) (F (toGf P g)))
    (law : ∀ κ (hJ : κ ∈ stdJ (LP)) (g : Formalism.AUTREP.GAf D.host.E V.rank),
        F (toGf P (g * κ)) = ((stdX (LP) ⟨κ, hJ⟩ : ℂˣ) : ℂ) • F (toGf P g)) :
    F ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (LE).J (LE).χ := by
  intro γ h k
  have hs : Function.Surjective (toGf P) := GlobalTheory.MtInRat.toGf_surjective P
  have key : ∀ (γ' : ReciprocityTheory.Aut.GQ D.host.E V.rank) (g k' : Formalism.AUTREP.GAf D.host.E V.rank) (hkJ : toGf P k' ∈ (LE).J),
      F (Bridge.ratF V (e γ') * toGf P g * toGf P k') = (((LE).χ ⟨_, hkJ⟩ : ℂˣ) : ℂ) • c.coef.ρ (e γ') (F (toGf P g)) := by
    intro γ' g k' hkJ
    have hQk := (LE).J_le hkJ
    have hr1 := red_J hr Pg Q chi xi red eG hred _ hkJ
    have hP : red ⟨_, hQk⟩ ∈ P₀ := by rw [hr1]; exact P₀.one_mem
    have hJ := (mem_stdJ_iff hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _).2 ⟨hQk, hP⟩
    have hX := stdX_eq hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _ hJ hQk hP
    have hch := (LE).ch_J ⟨_, hkJ⟩
    have h1 := hAut γ' (g * k')
    have h2 := law k' hJ g
    have e1 : Bridge.ratF V (e γ') * toGf P g * toGf P k' = toGf P (↑γ' * (g * k')) := by
      calc _ = toGf P (↑γ' * g) * toGf P k' := by rw [(hR γ').1, (toGf P).map_mul ↑γ' g]
        _ = toGf P (↑γ' * g * k') := ((toGf P).map_mul _ _).symm
        _ = _ := by rw [mul_assoc]
    have h1' : (⟨red ⟨_, hQk⟩, hP⟩ : P₀) = 1 := Subtype.ext hr1
    have hval : stdX (LP) ⟨k', hJ⟩ = (LE).χ ⟨_, hkJ⟩ := by
      rw [hX, h1', map_one, mul_one]
      exact hch
    refine (congrArg F e1).trans (h1.trans ((congrArg (c.coef.ρ (e γ')) h2).trans ((map_smul _ _ _).trans ?_)))
    rw [hval]
  have hgh : toGf P (Function.surjInv hs h) = h := Function.surjInv_eq hs h
  have hk' : toGf P (Function.surjInv hs k.1) = k.1 := Function.surjInv_eq hs k.1
  have hkJ : toGf P (Function.surjInv hs k.1) ∈ (LE).J := by rw [hk']; exact k.2
  have hk2 : (⟨_, hkJ⟩ : (LE).J) = k := Subtype.ext hk'
  have hmain := key (e.symm γ) (Function.surjInv hs h) (Function.surjInv hs k.1) hkJ
  rw [hk2, e.apply_symm_apply γ, hgh, hk'] at hmain
  exact hmain

set_option maxHeartbeats 4000000 in
theorem bwd_q (hg : V.gram = 1) (hU : UnitFr P)
    (red : (LE).Q →* G₀)
    (hred : ∀ q : (LE).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    {F : Bridge.Gf V → c.W}
    (law : ∀ κ (hJ : κ ∈ stdJ (LP)) (g : Formalism.AUTREP.GAf D.host.E V.rank),
        F (toGf P (g * κ)) = ((stdX (LP) ⟨κ, hJ⟩ : ℂˣ) : ℂ) • F (toGf P g))
    (κ : (LE).Q) (hκ : red κ ∈ P₀) (h : Bridge.Gf V) :
    F (h * κ) = (((LE).ch κ * ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h := by
  have hs : Function.Surjective (toGf P) := GlobalTheory.MtInRat.toGf_surjective P
  have key : ∀ (g k' : Formalism.AUTREP.GAf D.host.E V.rank) (hQ : toGf P k' ∈ (LE).Q) (hP : red ⟨_, hQ⟩ ∈ P₀),
      F (toGf P g * toGf P k') =
        (((LE).ch ⟨_, hQ⟩ * ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red ⟨_, hQ⟩, hP⟩ : ℂˣ) : ℂ) • F (toGf P g) := by
    intro g k' hQ hP
    have hJ := (mem_stdJ_iff hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _).2 ⟨hQ, hP⟩
    have hX := stdX_eq hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred _ hJ hQ hP
    refine ((congrArg F ((toGf P).map_mul g k')).symm.trans (law k' hJ g)).trans ?_
    rw [hX]
  have hgh : toGf P (Function.surjInv hs h) = h := Function.surjInv_eq hs h
  have hk' : toGf P (Function.surjInv hs κ.1) = κ.1 := Function.surjInv_eq hs κ.1
  have hQ : toGf P (Function.surjInv hs κ.1) ∈ (LE).Q := by rw [hk']; exact κ.2
  have hk2 : (⟨_, hQ⟩ : (LE).Q) = κ := Subtype.ext hk'
  have hP : red ⟨_, hQ⟩ ∈ P₀ := by rw [hk2]; exact hκ
  have hmain := key (Function.surjInv hs h) (Function.surjInv hs κ.1) hQ hP
  revert hP
  rw [hk2]
  intro hP hmain
  rw [hgh, hk'] at hmain
  exact hmain

set_option maxHeartbeats 4000000 in
theorem fwd_law (hg : V.gram = 1) (hU : UnitFr P)
    (red : (LE).Q →* G₀)
    (hred : ∀ q : (LE).Q, eG (red q) =
      rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)))
    {F : Bridge.Gf V → c.W}
    (hQc : ∀ (κ : (LE).Q) (hκ : red κ ∈ P₀) (h : Bridge.Gf V),
      F (h * κ) = (((LE).ch κ * ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ⟨red κ, hκ⟩ : ℂˣ) : ℂ) • F h)
    (κ : Formalism.AUTREP.GAf D.host.E V.rank) (hJ : κ ∈ stdJ (LP)) (g : Formalism.AUTREP.GAf D.host.E V.rank) :
    F (toGf P (g * κ)) = ((stdX (LP) ⟨κ, hJ⟩ : ℂˣ) : ℂ) • F (toGf P g) := by
  have hm := (mem_stdJ_iff hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred κ).1 hJ
  have hX := stdX_eq hr Pg Q chi xi hg hU red eG P₀ ψ₀ hred κ hJ hm.1 hm.2
  refine (congrArg F ((toGf P).map_mul g κ)).trans ?_
  rw [hX]
  exact hQc ⟨_, hm.1⟩ hm.2 (toGf P g)

end Main

set_option maxHeartbeats 4000000 in
theorem cutSp_iff_typeSp : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → UnitFr P → RatIso P e → ∀ (G₀ : Type) [Group G₀] (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch red P₀ ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ↔ (fun g => F (toGf P g)) ∈ NG.TypeSp (wtRep c e) (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) := by
  intro D V hr Pg Q chi xi c P e hg hU hR G₀ _ red eG P₀ ψ₀ hred F
  constructor
  · intro hF
    refine ⟨⟨fun γ g => fwd_rat hR hF.1 γ g, ?_⟩, fun κ => funext fun g => fwd_law hg hU red hred hF.2 κ.1 κ.2 g⟩
    have hC := (GlobalTheory.T.stdFrameLevelSubgroup_bounded_open_hyperspecial D V.rank (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)).2.1
    refine ⟨hC.choose, hC.choose_spec.1, fun κ hκ g => ?_⟩
    have hC' := hC.choose_spec.2 κ hκ
    refine (fwd_law hg hU red hred hF.2 κ hC'.1 g).trans ?_
    rw [hC'.2, Units.val_one, one_smul]
  · intro hF
    exact ⟨bwd_ad hg hU hR red hred hF.1.1 (fun κ hJ g => congrFun (hF.2 ⟨κ, hJ⟩) g),
      bwd_q hg hU red hred (fun κ hJ g => congrFun (hF.2 ⟨κ, hJ⟩) g)⟩

end GlobalTheory.MtInType
