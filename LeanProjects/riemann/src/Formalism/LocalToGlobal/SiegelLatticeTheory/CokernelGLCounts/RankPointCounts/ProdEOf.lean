import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem bOf_unique (a : Formalism.L2.SG.PairVal.GLR D) (b : Formalism.L2.SG.PairVal.MatR D)
    (hW : (a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b = ptMat w) : VolPinAsm.bOf w a = b := by
  have hWu := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit (K := D.host.E) w
  unfold VolPinAsm.bOf
  have h1 : (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * ptMat w
      = (ptMat w)⁻¹ * (((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) *
          ((a : Formalism.L2.SG.PairVal.MatR D) * ptMat w * b) := by rw [hW]
    _ = (ptMat w)⁻¹ * ((((a⁻¹ : Formalism.L2.SG.PairVal.GLR D)) : Formalism.L2.SG.PairVal.MatR D) * (a : Formalism.L2.SG.PairVal.MatR D)) *
          ptMat w * b := by simp only [Matrix.mul_assoc]
    _ = b := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul]

theorem mem_stabInt_glob (hA : ∀ p, Agree δ M p) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' δ M w) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ AP M δ u u' w p := by
  have hset : ∀ a : VolPinAsm.StG w, (a : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ↔
      ∀ p, πP M δ u u' w (hA p) a ∈ AP M δ u u' w p := by
    intro a
    obtain ⟨ha, hb, hW⟩ := bOf_spec w a
    rw [mem_stabIntSet_iff δ M u u' hA w]
    refine ⟨fun h p => ?_, fun hp => ⟨ha, _, hb, hW, hp⟩⟩
    obtain ⟨-, b, -, hW', hp⟩ := h
    have e := bOf_unique w (a : Formalism.L2.SG.PairVal.GLR D) b hW'
    rw [← e] at hp
    exact hp p
  constructor
  · intro hg

    set K : Subgroup (Formalism.L2.SG.PairVal.GLR D) :=
      (Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p)).map
        (VolPinAsm.StG w).subtype with hK
    have hle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ K := by
      unfold Formalism.L2.SG.PairVal.stabInt
      rw [Subgroup.closure_le]
      intro a ha
      have haSt : a ∈ VolPinAsm.StG w := by
        obtain ⟨h1, b, hb, hW, -⟩ := ha
        exact ⟨h1, b, hb, hW⟩
      refine ⟨⟨a, haSt⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob]
      exact (hset ⟨a, haSt⟩).1 ha
    obtain ⟨g', hg', e⟩ := hle hg
    have : g' = g := Subtype.ext e
    rw [this, SetLike.mem_coe, Formalism.L2.SG.Pf.ProdE.mem_glob] at hg'
    exact hg'
  · intro hp
    exact Subgroup.subset_closure ((hset g).2 hp)

theorem lOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    lOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = lOf δ M p L U * lOf δ M p g b * lOf δ M p L⁻¹ U⁻¹ := by
  rw [Matrix.mul_assoc L g, lOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), lOf_mul δ M hA g b L⁻¹ U⁻¹, Matrix.mul_assoc]

theorem ρOf_conj {p : PlF D} (hA : Agree δ M p) (L U g b : Formalism.L2.SG.PairVal.MatR D) :
    ρOf δ M p (L * g * L⁻¹) (U⁻¹ * b * U) = ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p g b * ρOf δ M p L U := by
  rw [Matrix.mul_assoc L g, ρOf_mul δ M hA L U (g * L⁻¹) (U⁻¹ * b), ρOf_mul δ M hA g b L⁻¹ U⁻¹]

theorem mem_CZ_glob (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) (g : VolPinAsm.StG w) :
    ((g : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L) ↔
      ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  rw [ZsVolGrp.mem_CZ M δ u u' Zh L hLdet]
  obtain ⟨ha, hb, hW⟩ := bOf_spec w g
  set gm : Formalism.L2.SG.PairVal.MatR D := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) with hgm
  set b := VolPinAsm.bOf w (g : Formalism.L2.SG.PairVal.GLR D) with hb'
  have hmemC : ∀ p, πP M δ u u' w (hA p) g ∈ CPL M δ u u' w (hA p) L U hL hU ↔
      Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) ∧
        Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p (L * gm * L⁻¹) (U⁻¹ * b * U)) := by
    intro p
    rw [lOf_conj M δ (hA p), ρOf_conj M δ (hA p)]
    rfl
  simp only [hmemC]
  constructor
  · rintro ⟨a', ha'eq, ha'lo, b', hb'up, hZ', hloc⟩ p
    have ea' : ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = L * gm * L⁻¹ := by
      have h := ha'eq
      rw [← hgm] at h
      rw [h]
      calc ((a' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
          = (L * L⁻¹) * (a' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) := by rw [hLi.2.2]; simp
        _ = L * (L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L) * L⁻¹ := by simp only [Matrix.mul_assoc]
    have eb' : b' = U⁻¹ * b * U := by
      have h1 : gm * ptMat w * (U * b' * U⁻¹) = ptMat w := by
        have := hZ'
        rw [hZ, ea'] at this
        have h2 : L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [this]
        calc gm * ptMat w * (U * b' * U⁻¹) = (L⁻¹ * L) * gm * (L⁻¹ * L) * ptMat w * U * b' * U⁻¹ := by
              rw [hLi.2.1]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
          _ = L⁻¹ * (L * gm * L⁻¹ * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
          _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := h2
          _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
          _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]
      have e := bOf_unique w (g : Formalism.L2.SG.PairVal.GLR D) _ h1
      rw [← hb'] at e
      rw [e]
      calc b' = (U⁻¹ * U) * b' * (U⁻¹ * U) := by rw [hUi.2.1]; simp
        _ = U⁻¹ * (U * b' * U⁻¹) * U := by simp only [Matrix.mul_assoc]
    obtain ⟨l, ρ, hl, hρ, hZl⟩ := hloc p
    obtain ⟨el, eρ⟩ := uniq δ M u u' (hA p) _ b' ha'lo hb'up l ρ (fun i => hl.1 i) (fun i => hρ.1 i) hZl
    rw [← ea', ← eb', ← el, ← eρ]
    exact ⟨hl, hρ⟩
  · intro hp
    set a'm := L * gm * L⁻¹ with ha'm
    have ha'lo : IsLoUni a'm := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hL ha) hLi.1
    have hb'up : IsUpUni (U⁻¹ * b * U) := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUi.1 hb) hU
    have hginv : ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * gm = 1 := by
      rw [hgm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hginv' : gm * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = 1 := by
      rw [hgm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    let a' : Formalism.L2.SG.PairVal.GLR D :=
      ⟨a'm, L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹,
        by
          calc a'm * (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹)
              = L * gm * (L⁻¹ * L) * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv', Matrix.mul_one, hLi.2.2],
        by
          calc (L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * L⁻¹) * a'm
              = L * ((((g : Formalism.L2.SG.PairVal.GLR D))⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * (L⁻¹ * L) * gm * L⁻¹ := by
                simp only [ha'm, Matrix.mul_assoc]
            _ = 1 := by rw [hLi.2.1, Matrix.mul_one, Matrix.mul_assoc L, hginv, Matrix.mul_one, hLi.2.2]⟩
    refine ⟨a', ?_, ha'lo, U⁻¹ * b * U, hb'up, ?_, fun p => ⟨_, _, (hp p).1, (hp p).2,
      move δ M u u' (hA p) a'm (U⁻¹ * b * U) ha'lo hb'up⟩⟩
    · show gm = L⁻¹ * a'm * L
      calc gm = (L⁻¹ * L) * gm * (L⁻¹ * L) := by rw [hLi.2.1]; simp
        _ = L⁻¹ * a'm * L := by simp only [ha'm, Matrix.mul_assoc]
    · show a'm * ZhatOM Zh * (U⁻¹ * b * U) = ZhatOM Zh
      rw [hZ]
      calc a'm * (L * ptMat w * U) * (U⁻¹ * b * U) = L * gm * (L⁻¹ * L) * ptMat w * (U * U⁻¹) * b * U := by
            simp only [ha'm, Matrix.mul_assoc]
        _ = L * (gm * ptMat w * b) * U := by
            rw [hLi.2.1, hUi.2.2, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = L * ptMat w * U := by rw [hW]

theorem idxRatio_self {G : Type} [Group G] (A : Subgroup G) : Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A A = 1 := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio; simp [Subgroup.relIndex_self]

theorem idxRatio_subgroupOf {G : Type} [Group G] (A B K : Subgroup G) (hA : A ≤ K) (hB : B ≤ K) :
    Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio (A.subgroupOf K) (B.subgroupOf K) = Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio A B := by
  unfold Formalism.L2.SG.Pf.IndexCocycleOrbits.IdxRatio
  rw [Subgroup.relIndex_subgroupOf hA, Subgroup.relIndex_subgroupOf hB]

theorem cz_le (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (Zh : Formalism.L2.SG.PairVal.MatR D) (hZ : ZhatOM Zh = L * ptMat w * U) :
    Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' Zh L ≤ VolPinAsm.StG w := by
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLdet : IsUnit L.det := by rw [ZsVolGrp.det_lo (fun a => (hL a a).2 rfl) (fun a b h => (hL a b).1 h)]; exact isUnit_one
  intro a ha
  rw [ZsVolGrp.mem_CZ M δ u u' Zh L hLdet] at ha
  obtain ⟨a', ha'eq, ha'lo, b', hb'up, hZ', -⟩ := ha
  refine ⟨?_, U * b' * U⁻¹, ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hU hb'up) hUi.1, ?_⟩
  · rw [ha'eq]; exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLi.1 ha'lo) hL
  · rw [ha'eq]
    rw [hZ] at hZ'
    calc L⁻¹ * (a' : Formalism.L2.SG.PairVal.MatR D) * L * ptMat w * (U * b' * U⁻¹)
        = L⁻¹ * ((a' : Formalism.L2.SG.PairVal.MatR D) * (L * ptMat w * U) * b') * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L⁻¹ * (L * ptMat w * U) * U⁻¹ := by rw [hZ']
      _ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLi.2.1, hUi.2.2, Matrix.one_mul, Matrix.mul_one]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_of (hap : ApproxC M δ u u' F0 what₂) (hloc : LocIdxC M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') := by
  intro γ w F' L U hE
  obtain ⟨S, hS, hfin, happrox⟩ := hap γ w F' L U hE
  have hA := hE.1
  have hL : IsLoUni L := hE.2.2.2.2.2.2.2.1
  have hU : IsUpUni U := hE.2.2.2.2.2.2.2.2.1
  have hZ : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U := hE.2.2.2.2.2.2.2.2.2
  have hset : Formalism.L2.SG.PairVal.stabIntSet D u u' δ M w ⊆ Formalism.L2.SG.Pf.StabilizerIndexVolumes.StSet (ptMat w) := by
    intro a ha
    obtain ⟨h1, b, hb, hW, -⟩ := ha
    exact ⟨h1, b, hb, hW⟩
  have hAle : Formalism.L2.SG.PairVal.stabInt D u u' δ M w ≤ VolPinAsm.StG w := fun x hx =>
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.closure_subset_StSet Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed _ _ hset hx
  have hCle := cz_le M δ u u' w L U hL hU _ hZ
  rw [← idxRatio_subgroupOf _ _ _ hAle hCle]
  have e1 : (Formalism.L2.SG.PairVal.stabInt D u u' δ M w).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => AP M δ u u' w p) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_stabInt_glob M δ u u' w hA g
  have e2 : (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u' (ZhatL (lf D F0) F') L).subgroupOf (VolPinAsm.StG w) =
      Formalism.L2.SG.Pf.ProdE.glob (fun p => πP M δ u u' w (hA p)) (fun p => CPL M δ u u' w (hA p) L U hL hU) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Formalism.L2.SG.Pf.ProdE.mem_glob]
    exact mem_CZ_glob M δ u u' w hA L U hL hU _ hZ g
  rw [e1, e2, Formalism.L2.SG.Pf.ProdE.idxRatio_glob _ _ _ S hS (fun p => (hfin p).1) (fun p => (hfin p).2) happrox]
  have hl := fun p => hloc γ w F' L U hE p
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  · exact Finset.prod_congr rfl fun p _ => hl p
  · intro p hp
    by_contra hpS
    apply hp
    show Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
      (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) = 1
    rw [← hl p, hS p hpS, idxRatio_self]

end Formalism.L2.SG.Pf.ProdE
