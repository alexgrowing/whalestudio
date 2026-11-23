import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VFormCong

theorem redFn_eq_one_of_finCong {D : D7} {V : TH.HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {N : ℕ} {k : GA D V}
    (hΛ : IsSDFrame V β Λ 1) (hN : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hk : GlobalTheory.Member.FinCong V N k) :
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V N a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V a).1 *ᵥ z - z = N • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ N _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, hred⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Lev.finE V k)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) N hfr (hc k hk) hc'
  have hy' : Formalism.L2.DIV.frGL β y = Lev.finE V k := hy
  intro PP hP
  rw [← hy', Formalism.L2.DIV.redFn_frGL]
  refine hred _ _ ?_
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hN PP hP)

theorem levFn_eq_one {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n)
    (x : GL (Fin n) (Lev.EAf D)) (h3 : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP x = 1) :
    Formalism.L2.DIV.levFn β L x = 1 := by
  have e : Formalism.L2.DIV.levFn β L x = Formalism.L2.DIV.levFn β L 1 := by
    have hr : Formalism.L2.DIV.rTup β L x = Formalism.L2.DIV.rTup β L 1 := by
      funext PP
      show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 x) = Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 1)
      rw [h3 PP.1 (Or.inl PP.2), Formalism.L2.DIV.redFn_one]
    unfold Formalism.L2.DIV.levFn
    rw [hr]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => by
        rw [h3 PP (Or.inl hPP), Formalism.L2.DIV.redFn_one]
    · exact Finset.prod_congr rfl fun PP hPP => by
        rw [h3 PP (Or.inr hPP), Formalism.L2.DIV.redFn_one]
  rw [e]
  exact (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) β L).map_one

end GlobalTheory.VFormCong

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.VFormCong.exists_cong_levEnv : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  intro D cf nch tp X M rep hA j t
  classical
  obtain ⟨N, hN0, hNmem⟩ : ∃ N : ℕ, 0 < N ∧ ∀ PP, PP ∈ (X.R.datVt j t).Pg ∨ PP ∈ (X.R.datVt j t).Q →
      ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    refine ⟨∏ PP ∈ (X.R.datVt j t).Pg ∪ (X.R.datVt j t).Q, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ =>
      Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun PP hPP => ?_⟩
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP => Ideal.absNorm (IsDedekindDomain.HeightOneSpectrum.asIdeal PP))
      (Finset.mem_union.2 hPP)
    rw [hu, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  obtain ⟨N', hN', hcong⟩ :=
    GlobalTheory.StdFrameCong.exists_cong_finCong D (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) N hN0
  refine ⟨N', hN', fun κ hκ => ?_⟩
  have hk := hcong κ hκ
  have hβ := X.given.core.lev.βV j
  refine ⟨GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Vc D j) (X.R.βV j) (X.R.ΛV j) (X.R.datVt j t) N _ hβ hNmem hk, ?_⟩
  apply Units.ext
  change ((Formalism.L2.DIV.levFn (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) (Lev.finE (Vc D j) ((hA.PV j).ψ κ)) : ℂˣ) : ℂ) = 1
  rw [GlobalTheory.VFormCong.levFn_eq_one (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) _
    (fun PP hP => GlobalTheory.VFormCong.redFn_eq_one_of_finCong (X.R.datVt j t) hβ hNmem hk PP hP)]
  rfl
