import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatScal

noncomputable section

open GlobalTheory.LocMod (Place Frame IsOne)
open GlobalTheory.SplitWeil (SB)
open GlobalTheory.SplitFlip (Grid Edge oppositePath gdet)
open GlobalTheory.FlatPlace

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def xiEdge (ξ : kˣ →* ℂˣ) : Edge → kˣ →* ℂˣ
  | .theta _ _ => ξ
  | .ex _ _ => 1

theorem kappa_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ) (b : Edge) (X : ℕ × ℕ) :
    Γ.kappa b X = ({Γ with mu := μ₀} : Grid k).kappa b X * xiEdge ξ b := by
  cases b with
  | theta i j =>
    show Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) = μ₀ (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) * ξ
    rw [h, mul_div_right_comm]
  | ex i j =>
    show Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) = Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) * 1
    rw [mul_one]

def xiPart (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) : ℂˣ :=
  ((oppositePath Γ.m).map fun b => xiEdge ξ b (gdet (g b.src)) * (xiEdge ξ b (gdet (g b.tgt)))⁻¹).prod

theorem charFactor_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ)
    (g : Γ.VertexGroup) :
    charFactor Γ g = charFactor ({Γ with mu := μ₀} : Grid k) g * xiPart Γ ξ g := by
  simp only [charFactor, xiPart, kappa_split Γ μ₀ ξ h, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  simp only [MonoidHom.mul_apply, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem xiPart_mem (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) (H : Subgroup ℂˣ) (hH : ∀ x, ξ x ∈ H) :
    xiPart Γ ξ g ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  have e : ∀ u, xiEdge ξ b u ∈ H := fun u => by
    cases b with
    | theta _ _ => exact hH u
    | ex _ _ => exact H.one_mem
  exact H.mul_mem (e _) (H.inv_mem (e _))

theorem prod_edgeFactor (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod = ((charFactor Γ ε : ℂˣ) : ℂ) := by
  rw [charFactor, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  have ha : ∀ X (z : ℂ), GlobalTheory.SplitFlip.apow (gdet (GlobalTheory.SplitFlip.Assignment.one.read (ε X))) z = 1 := fun X z => by
    refine GlobalTheory.SplitFlip.apow_of_valuation_eq_one ?_ z
    rw [show GlobalTheory.SplitFlip.Assignment.one.read (ε X) = GlobalTheory.SplitFlip.invT (ε X) from rfl, GlobalTheory.SplitFlip.gdet_invT,
      Units.val_inv_eq_inv_val, map_inv₀, GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X), inv_one]
  simp only [Grid.edgeFactor, ha, mul_one, Function.comp, Units.coeHom_apply, Units.val_mul]

theorem charFactor_eq_one (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _)
    (hrow : ∀ i < Γ.m, ε (i, Γ.m) = 1 ∧ ε (i + 1, Γ.m) = 1)
    (hμ : ∀ j < Γ.m, IsUnram (Γ.mu (j + 1))) (hη : IsUnram Γ.eta) : charFactor Γ ε = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · show Γ.kappa _ (i, Γ.m) (gdet (ε (i, Γ.m))) * (Γ.kappa _ (i + 1, Γ.m) (gdet (ε (i + 1, Γ.m))))⁻¹ = 1
    have g1 : ∀ n, gdet (1 : GL (Fin n) k) = 1 := fun _ => map_one _
    rw [(hrow i hi).1, (hrow i hi).2, g1, g1, map_one, map_one, inv_one, mul_one]
  · have hu : ∀ X, Γ.kappa (.theta Γ.m j) X (gdet (ε X)) = 1 := fun X => by
      have hv := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X)
      show (Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2)) (gdet (ε X)) = 1
      rw [MonoidHom.div_apply, MonoidHom.pow_apply, hμ j hj _ hv, hη _ hv, one_pow, div_one]
    show Γ.kappa _ _ (gdet (ε _)) * (Γ.kappa _ _ (gdet (ε _)))⁻¹ = 1
    rw [hu, hu, inv_one, mul_one]

end Local

section Grid0

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

variable (G : GridData L sc) in

def grid0 (w : Pl D.host.E) : Grid (Kw w) where
  m := D.R.m
  r := D.R.r
  t := D.R.t
  s := sLen D
  mu j := (muBase L j).loc w
  chi i := (G.ch.chiH i).loc w
  eta := L.C.eta.loc w

variable (G : GridData L sc) in
open Classical in

def eps0 (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j ∈ idx D then GlobalTheory.SplitFlip.diagGL fun a =>
    if Odd j ∧ topRank (grid0 G w) j + (D.R.m - 1 - j) / 2 ≤ a.1 then Units.map (Int.castRingHom (Kw w)).toMonoidHom (-1) else 1
    else 1

variable (G : GridData L sc) in

def stair0 (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j + 2 ≤ D.R.m then stair (grid0 G w) (unifAt w) (cosExp G w) j else 1

theorem elt_stair (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i + 1))) :
    (repsAt G t w).elt β = (stair0 G w : (locGrid G t w).VertexGroup) := by
  have hb : β = fun i : Fin _ => DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i.1 + 1)) := funext hβ
  subst hb
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = D.R.m
  · subst hi
    have e1 : (stair0 G w : (locGrid G t w).VertexGroup) (D.R.m, j) =
        if j + 2 ≤ D.R.m then stair (locGrid G t w) (unifAt w) (cosExp G w) j else 1 := onColumn_apply (G := grid0 G w) _ j
    rw [e1]
    split_ifs with hj
    · exact through_elt _ hj
    · exact elt_eq_one t w _ (by omega)
  · show onColumn (G := locGrid G t w) _ (i, j) = onColumn (G := grid0 G w) _ (i, j)
    rw [onColumn, onColumn, dif_neg (show ¬ (i, j).1 = (locGrid G t w).m from hi),
      dif_neg (show ¬ (i, j).1 = (grid0 G w).m from hi)]
    rfl

end Grid0

open Classical in

theorem scal : Big fun ch => ScalP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  refine ⟨fun w => if w ∈ ch.G.pl.W0 then
      ((charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w) : ℂˣ) : ℂ) else 1,
    fun t w => (xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
      if w ∈ ch.G.pl.W0 then xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w) else 1)⁻¹,
    fun t w => ?_, fun w hw => if_neg hw, fun t w hw β hβ => ?_⟩
  · have hH : ∀ x, (R.toLevCh.xiH t).loc w x ∈ xiVals R.toLevCh t := fun x => Subgroup.subset_closure ⟨w, x, rfl⟩
    refine inv_mem (mul_mem (xiPart_mem _ _ _ _ hH) ?_)
    split_ifs
    · exact xiPart_mem _ _ _ _ hH
    · exact one_mem _
  · have hmu : ∀ j, (locGrid ch.G t w).mu j = (fun j => (muBase R.toLevCh j).loc w) j * (R.toLevCh.xiH t).loc w :=
      fun j => MonoidHom.ext fun _ => rfl
    have hsplit := charFactor_split (locGrid ch.G t w) _ _ hmu
    dsimp only
    unfold zetaLoc
    rw [prod_edgeFactor _ _ (epsV_mem t w)]
    by_cases h0 : w ∈ ch.G.pl.W0
    · have hk : keepAt ch.G w = false := by simp [keepAt, h0]
      rw [hk, if_pos h0, if_pos h0, elt_stair ch.G t w β (hβ h0)]
      have key : charFactor (locGrid ch.G t w) (epsV ch.G t w) * charFactor (locGrid ch.G t w) (stair0 ch.G w) =
          (charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w)) *
          ((xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
            xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w))⁻¹)⁻¹ := by
        rw [inv_inv, hsplit (epsV ch.G t w), hsplit (stair0 ch.G w)]
        exact mul_mul_mul_comm _ _ _ _
      simp only [Bool.false_eq_true, if_false]
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val key
    · have hk : keepAt ch.G w = true := by simp [keepAt, h0]
      rw [hk, if_neg h0, if_neg h0, if_pos rfl]
      have ha : w.under (𝓞 D.host.F) ∉ ch.G.pl.S0 := by
        rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, b⟩ | ⟨a, -, -⟩
        · exact absurd (by rw [b]; exact Finset.mem_image_of_mem ch.G.pl.w a) h0
        · exact a
      have hoff : ∀ i j, i ≠ D.R.m → epsV ch.G t w (i, j) = 1 := fun i j hi => by
        show onColumn (G := locGrid ch.G t w) _ (i, j) = 1
        rw [onColumn, dif_neg (show ¬ (i, j).1 = (locGrid ch.G t w).m from hi)]
      have h1 : charFactor ({locGrid ch.G t w with mu := fun j => (muBase R.toLevCh j).loc w} : Grid (Kw w))
          (epsV ch.G t w) = 1 := by
        refine charFactor_eq_one _ _ (epsV_mem t w) (fun i hi => ⟨hoff i _ (Nat.ne_of_lt hi), ?_⟩) (fun j hj => ?_) ?_
        · by_cases e : i + 1 = D.R.m
          · show epsV ch.G t w (i + 1, D.R.m) = 1
            rw [show (i + 1, D.R.m) = (D.R.m, D.R.m) by rw [e]]
            exact epsV_eq_one t w (by omega)
          · exact hoff _ _ e
        · replace hj : j < D.R.m := hj
          show IsUnram ((muBase R.toLevCh (j + 1)).loc w)
          rw [muBase, dif_pos hj]
          refine GlobalTheory.FunObj.Good.isUnram_loc.2 ((R.toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
          refine ha (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
          have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
            show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
            rw [map_natCast]; exact hk
          fin_cases k
          · exact Or.inl this
          · exact Or.inr (Or.inl this)
        · exact GlobalTheory.FunObj.Good.isUnram_loc.2 (R.toLevCh.C.isEta.unr w)
      simp only [hsplit (epsV ch.G t w), h1, one_mul, mul_one, Units.val_inv_eq_inv_val, inv_inv]

end

end GlobalTheory.FlatScal
