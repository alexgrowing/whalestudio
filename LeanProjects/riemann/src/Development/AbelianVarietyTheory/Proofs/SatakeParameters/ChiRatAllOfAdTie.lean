import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwUChiRat

open GlobalTheory.TwU Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG NumberField IsDedekindDomain

section Gen

variable {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
  (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)
  (Rel : SB → (Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) → X.K → Prop)

theorem exists_isOver (Q : HeightOneSpectrum (𝓞 D.host.E)) : ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v Q := by
  refine ⟨⟨Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, ?_⟩, rfl⟩
  intro h
  have hN : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 D.host.F) ∈ Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hN
  have : Ideal.absNorm Q.asIdeal = 0 := by exact_mod_cast hN
  exact Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)

theorem chiRatAll_of_le (hLe : LocLe s lev fb dep Rel) (hChi : ChiIs s lev fb dep Rel)
    (hK : ∀ y : X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = s.σ₀ y) : ChiRatAll lev D.what₂.embLL := by
  classical
  intro κ
  have hv : ∀ P : SB, ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP s P.1) := fun P => exists_isOver (seamP s P.1)
  choose v hv using hv
  have hU := (lev.U_eq κ.1).1 κ.2
  have hgz : ∀ P : SB, ∃ g z, Rel P g z ∧ InFrame s fb dep P κ.1 g := fun P => hLe P (v P) (hv P) κ.1 hU.1 (hU.2 (v P))
  choose g z hgz using hgz
  have h1 := hChi κ g z hgz
  obtain ⟨k, hk⟩ := hK (∏ P, z P)
  refine ⟨k⁻¹, ?_⟩
  rw [map_inv₀, hk]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end Gen

theorem chiRatAll_of_adTie : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ) (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), GlobalTheory.TwU.AdTie A dtU a → (∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y) → ∀ i hi β, ChiRatAll ((St i hi).K β).lev D.what₂.embLL := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ St A dtU a H hK i hi β
  have hm := m_eq t μ
  rcases Nat.lt_or_ge t.m2 i with h | h
  · rcases Nat.lt_or_ge (t.m2 + 1) i with h' | h'
    · obtain rfl : i = t.m2 + 1 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levTop β).1 (H.levTop β).2 hK
    · obtain rfl : i = t.m2 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levCpl β).1 (H.levCpl β).2.2 hK
  · have hlt : i < D.R.m := by omega
    exact chiRatAll_of_le t.seam _ _ _ _ (H.levMid i hlt h β).1 (H.levMid i hlt h β).2.2 hK

end GlobalTheory.TwUChiRat
