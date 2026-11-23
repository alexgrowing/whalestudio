import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalComponentData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos
namespace GlobalTheory.LineOffT
variable {D : D7}
theorem lat_zero_line_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v' : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v') (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), f.c.Is → v'.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v' → ShapeOff v' o → GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v' o G → GlobalTheory.MiTop.PrimTop (c := f.c) v'.tP o.ζ₀ → ∀ x : GlobalTheory.FinPl.Pl D, x ∉ v'.gP → x ∉ v'.tP → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ x.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = x), ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) (v'.N 0) (· = x) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = x)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B k _ _ _ _ ι v o n G pl hc _ _ sh _ _ hb hp x _ hx u'' hu'' a ha
  have hTp : (D.mem u'').A.T.Prime := (D.mem u'').A.T_prime
  have hcop : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.mem u'').A.T := by
    obtain ⟨P, hP⟩ := exists_place D.host.E hTp
    refine ((Nat.Prime.coprime_iff_not_dvd hTp).2 fun ⟨t, ht⟩ => hW.aa P (Or.inr (Or.inr ⟨u'', hP⟩)) ?_).symm
    rw [ht, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hP
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hc.std
  have hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE f.c.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x) := fun s hs => by
    rw [(hα x).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have uξ := isU_xi_of_prime hTp hu'' (D.T_ne_d u'') hcop
  have uα := isU_alpha_of_prime hTp hu'' (UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u'')) (D.T_ne_q u'') (D.T_ne_d u'') hcop sh.pre.line (hα x).1
  have ug : IsU x (incA D (W.S.X.B.g : D.host.E)) := by
    refine isU_nat (UnitAt.notMem_of_coprime hu'' ?_)
    rw [W.S.X.g_eq]
    exact Nat.Coprime.mul_left ((Nat.coprime_primes (D.host.g_prime 0) hTp).2 (D.T_ne_g u'' 0).symm)
      ((Nat.coprime_primes (D.host.g_prime 1) hTp).2 (D.T_ne_g u'' 1).symm)
  have uc : IsU x (cU α : AE D) := uα.conj
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := GlobalTheory.LineIdeal.first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 ⟨0, hr⟩ rfl
  have hI := GlobalTheory.LineIdeal.all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 hx (hα x).1 hψ 0 D.R.rS h₀ (D.R.rS - 1) ⟨0, hr⟩ (by simp only; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  rw [← mul_assoc (α * α), ← mul_assoc ((xiU D * α * cU α) ^ _)] at hI
  have uK : IsU x (((xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) := by
    have h1 : IsU x (((xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := (uξ.mul uc).inv (xiU D * cU α).mul_inv
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact (((uξ.mul uα).mul uc).pow _).mul ((uα.mul uα).mul ((uα.mul h1).pow _))
  generalize (xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI uK
  have uS : IsU x (incA D (-s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS))) := by
    have h1 : IsU x (incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) := by
      rw [map_mul, map_pow, map_pow]
      exact (IsU.pow (u := incA D D.host.xi0) uξ _).mul (ug.pow _)
    rcases hs with rfl | rfl
    · rw [neg_one_mul, map_neg]; exact h1.neg
    · rwa [neg_neg, one_mul]
  have hg0 : (W.S.X.B.g : D.host.E) ≠ 0 := by
    rw [W.S.X.g_eq]
    exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  obtain ⟨w, hw⟩ : ∃ w, w = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := hw ▸ mul_ne_zero hs0 (mul_ne_zero hμ (pow_ne_zero _ hg0))
  have hlw : -s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS) = lam * w := by
    rw [hw]
    linear_combination (-s * (W.S.X.B.g : D.host.E) ^ D.R.rS) * n1
  rw [← hw] at he
  rw [hlw, map_mul] at uS
  have e1 : incA D w * incA D w⁻¹ = 1 := (inU w hw0).mul_inv
  have hy : (fun i => a * incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) =
      colMul B.d.jX ⟨0, hr⟩ (incA D w⁻¹ * a) := by
    funext i
    change _ = _ * incA D (B.d.e i ⟨0, hr⟩)
    rw [he, map_mul]
    generalize incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i))) = t
    linear_combination (-a * t) * e1
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI (incA D w⁻¹ * a) (Ideal.mul_mem_left _ _ ha)
  rw [← hj] at h1
  refine (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hy)).trans (h1.trans ?_)
  rw [(uK.mul uS) _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))]
  have e2 := (K * inU lam hlam).mul_inv
  rw [Units.val_mul, inU_val] at e2
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D w * incA D w⁻¹ * a) * e2 + a * e1
end GlobalTheory.LineOffT
end
end
