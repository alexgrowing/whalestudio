import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeActionFramedPointsOfUnipotentModTwoPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowWeightGramAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowGramAlgebraicSectionStatement
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem mem_smul_top_of_coprime {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (I J : Ideal R) (hIJ : J ⊔ I = ⊤)
    (f : N →ₗ[R] N) (h : ∀ z ∈ J • (⊤ : Submodule R N), f z ∈ I • (⊤ : Submodule R N)) (x : N) :
    f x ∈ I • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : R) ∈ J ⊔ I)
  have e : f x = f (a • x) + b • f x := by rw [map_smul, ← add_smul, hab, one_smul]
  rw [e]
  exact add_mem (h _ (Submodule.smul_mem_smul ha Submodule.mem_top)) (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem natCast_not_isUnit {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : g.Prime) : ¬ IsUnit (g : 𝓞 K) := by
  intro hu
  have h1 := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
  have e : ((g : 𝓞 K)) = algebraMap ℤ (𝓞 K) (g : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at h1
  have := hg.two_le
  rcases h1 with h1 | h1 <;> omega

theorem sup_span_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    {g : ℕ} (hg : g.Prime) (hd : g ∣ l.M) : l.Mb ⊔ Ideal.span {(g : 𝓞 E)} ≠ ⊤ := by
  intro htop
  have hb : Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    have := congrArg (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E)) htop
    rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_top] at this
  have hle : (⊤ : Ideal (𝓞 E)) ≤ Ideal.span {(g : 𝓞 E)} := by
    calc (⊤ : Ideal (𝓞 E)) = (l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) * (Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) l.Mb ⊔ Ideal.span {(g : 𝓞 E)}) := by
          rw [htop, hb, Ideal.top_mul]
      _ ≤ Ideal.span {(g : 𝓞 E)} := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
          refine sup_le (sup_le ?_ (Ideal.mul_le_inf.trans inf_le_right)) (sup_le (Ideal.mul_le_inf.trans inf_le_left) (Ideal.mul_le_inf.trans inf_le_left))
          rw [Ideal.span_singleton_le_span_singleton]
          exact_mod_cast (Nat.cast_dvd_cast hd : ((g : 𝓞 E)) ∣ (l.M : 𝓞 E))
  exact natCast_not_isUnit hg (Ideal.span_singleton_eq_top.1 (top_le_iff.1 hle))

theorem free_base : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by omega⟩
  have hpq : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    have h1 := (p.fw.laws.pins.2.2.2 _ hj).1
    have h2 := D.R.m_add_three_le_k
    rw [h1]
    simp only [Ranks.sigW]
    omega
  have hun : ∀ (g : (p.F.lv2.lvl false).P) (x : (p.T.Q.Dw ((i : ℕ) + 1)).La),
      (((p.O i).lev (g : p.P.Gp) - 1) ^ D.R.r) x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) :=
    fun g x => mem_smul_top_of_coprime _ _ (by rw [sup_comm]; exact p.T.Q.l.coprime) _
      (GlobalTheory.T.final_row_weight_gram_algebraic p i PP A M hR hi hG hW hH hF g) x
  exact GlobalTheory.T.free_action_framedPoints_of_unipotent_mod_two_primes D.host.E p.T.Q.H (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
    (p.F.lv2.lvl false).P (fun g => (p.O i).lev (g : p.P.Gp)) D.R.r (D.host.g 0) (D.host.g 1)
    (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.E)}) (p.T.Q.l.Mb ⊔ Ideal.span {((D.host.g 1 : ℕ) : 𝓞 D.host.E)})
    hpq (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
    (sup_span_ne_top _ (D.host.g_prime 0) (by rw [hM]; exact dvd_mul_right _ _))
    (sup_span_ne_top _ (D.host.g_prime 1) (by rw [hM]; exact dvd_mul_left _ _))
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    le_sup_left le_sup_left (fun g x => Submodule.smul_mono_left le_sup_left (hun g x))
    (fun g x => Submodule.smul_mono_left le_sup_left (hun g x)) (GlobalTheory.T.final_row_gram_algebraic_section p i PP A M hR hi hG hW hH hF)

end GlobalTheory.DefFree
