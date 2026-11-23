import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DefIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ConjVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBstab
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpVars
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpRels
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemSpanX
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpOddSpanX
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NegOneZpowSg
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsPaddedFamily
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGbox
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZeroOfNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpDimb
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CwZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrpOfMemSucc
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LieTMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpHasobs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpMazur

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sum_ge {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (m : ℕ) (e : F.V → ℕ)
    (h : ∀ v, m ≤ e v) : m * F.d ≤ ∑ v, F.dv v * e v := by
  unfold Frame.d
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (h v)

private theorem sum_le {I : Type} [Fintype I] (m : ℕ) (e : I → ℕ) (h : ∀ v, e v ≤ m) :
    ∑ v, e v ≤ m * Fintype.card I := by
  have := Finset.sum_le_card_nsmul Finset.univ e m (fun v _ => h v)
  simpa [mul_comm] using this

theorem UpperTheory.V.Fr.epres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → Nonempty L.EPres := by
  intro l _ O _ _ _ _ F C₀ hok S x L hx
  obtain ⟨σ, hσ⟩ := ep_inv hok S x L hx
  have hbarL := pr_res hok (Or.inr rfl) S x L
  obtain ⟨φ, hφ⟩ := hbarL.1
  have hgood := pr_good hok (Or.inr rfl) (ResidueField L.O') φ _ hφ
  have h2K : (2 : ResidueField L.O') ≠ 0 := hgood.1.two
  have h2 : IsUnit (2 : L.O') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_ofNat]
    exact h2K
  have hloc := loc_rho hok (Or.inr rfl) S x L
  have hU : NRep.Univ L.O' L.ρ := ⟨hloc.1, fun C _ _ _ ρ' hc hb => def_iso hok (Or.inr rfl) S x L C ρ' hc hb⟩
  obtain ⟨B₀, hB₀, hB₀c⟩ := pr_box hok L.R (maximalIdeal L.R) L.ρ hloc.1
    (fun v => flag hok (Or.inr rfl) S L.R (L.ι : S.A →+* L.R) v)
  obtain ⟨B, π, hBo, hBr, hG⟩ := ep_gbox L.O' h2 hok.del_c L.R σ hσ.sq L.ρ B₀ hB₀ hgood.1 hσ.ent
    (fun v i s => hσ.base (S.ψB v i s))
  have hBc : Box.Cont (maximalIdeal L.R) B := by
    unfold Box.Cont
    rw [hBr]
    exact hB₀c
  have hEv := ep_ev L.O' h2 L.R σ B π hG
  have htan := ep_tan hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv hgood.2.1 hgood.2.2
  obtain ⟨a, g, p, hsurj, hvar, hpart, hhom, hmin⟩ := ep_vars L.O' h2 L.R σ hσ.sq
  obtain ⟨κ, _, f, wf, hf, hker, hind⟩ := ep_rels L.O' h2 (Fin a ⊕ Fin g) (Space.Loc.par a g) (RingHom.ker p) hhom
  let P : GPres L.O' σ := ⟨a, g, p, κ, f, wf, hsurj, hvar, hpart, hhom, hmin, hf, hker, hind⟩
  have hee : L.ρ.ee = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (Sum.inr i))) := by
    rw [ep_ee hok S x L hx σ hσ, ep_odd L.O' L.R σ P]
  have hBbOf : (Box.bar L.O' B).Of (NRep.bar L.O' L.ρ) := hBo.map _
  have hdual := pr_dual hok (Or.inr rfl) (ResidueField L.O') φ (NRep.bar L.O' L.ρ) (Box.bar L.O' B) hBbOf hφ hbarL.2
  have hprp := ep_prp h2K (Box.bar L.O' B) π hEv
  have hopen := (pr_open hok L.O' L.R B hBc).2.1
  have hopenj : ∀ j, IsOpen ((hEv.ad j).ker : Set F.Γ) := by
    intro j
    apply Subgroup.isOpen_mono _ hopen
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    simp [Box.Ev.ad_apply, hs]
  have hstab : ∀ j (v : F.V) (s : F.Gv v), ∀ X ∈ (Box.bar L.O' B).bp j v, (hEv.ad j (F.loc v s)) X ∈ (Box.bar L.O' B).bp j v := by
    intro j v s X hX
    simp only [Box.bp, Submodule.mem_comap, Submodule.subtype_apply] at hX ⊢
    rw [Box.Ev.ad_apply]
    exact pr_bstab _ _ v s _ hX
  have EC := fun j => hok.ec (ResidueField L.O') (adp (ResidueField L.O') j) (hEv.ad j) ((Box.bar L.O' B).bp j) (hopenj j) (hstab j) (hprp.2 j _ hdual)
  have hder := ep_der L.O' h2 L.R σ P
  have hdimb := ep_dimb h2K (Box.bar L.O' B) π hEv
  have hcw := fun w => ep_cw h2K (Box.bar L.O' B) π hEv (F.cw w) (hok.cw_sq w) (hok.del_cw w)
  refine ep_pad S x L σ hσ P ?_ ?_ hee
  · haveI := (EC 0).1
    have hm := ep_mazur L.O' h2 L.R σ hσ.sq P 0 _ (ep_hasobs hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv 0)
    have hs1 : 4 * F.d ≤ ∑ v, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).bp 0 v) :=
      sum_ge F 4 _ (fun v => (hdimb v).1)
    have hs2 : ∑ w, Module.finrank (ResidueField L.O') ((hEv.ad 0 (F.cw w)) - 1).ker ≤ 1 * Fintype.card F.Inf :=
      sum_le 1 _ (fun w => (hcw w).1)
    rw [hok.card_inf] at hs2
    have e := (EC 0).2
    have t := htan.2
    have d0 := hder.2.1
    omega
  · haveI := (EC 1).1
    have hm := ep_mazur L.O' h2 L.R σ hσ.sq P 1 _ (ep_hasobs hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv 1)
    have hs1 : 2 * F.d ≤ ∑ v, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).bp 1 v) :=
      sum_ge F 2 _ (fun v => (hdimb v).2)
    have hs2 : ∑ w, Module.finrank (ResidueField L.O') ((hEv.ad 1 (F.cw w)) - 1).ker ≤ 2 * Fintype.card F.Inf :=
      sum_le 2 _ (fun w => (hcw w).2)
    rw [hok.card_inf] at hs2
    have e := (EC 1).2
    have t := htan.1 1
    have d1 := hder.2.2
    omega
