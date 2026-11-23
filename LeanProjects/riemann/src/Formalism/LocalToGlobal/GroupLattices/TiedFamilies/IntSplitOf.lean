import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsHyp
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem intSplit_of (I : LocId L p nV W Qq) : Cmp.IntSplit I := fun v t =>
  split_integral_completion F E (I.plc v) (Cmp.splV I v) (fun a => I.spl_alg _ _ a) t

theorem hypAtP_C (I : LocId L p nV W Qq) (hb : Cmp.NotBad I) (hs : Cmp.SelfDualAtP I) : Cmp.HypAtP I :=
  Cmp.isHyperbolicAt_of_integralSplit I hb (intSplit_of I) hs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_notMem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p n : ℕ} (hp : p.Prime)
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (hn : ¬ p ∣ n) : (n : 𝓞 F) ∉ v.asIdeal := by
  intro hn'
  have hc : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have h1 : ((a * p + b * n : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hn')
  rw [hab, Int.cast_one] at h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem notBad_C (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') : Cmp.NotBad I := by
  unfold Cmp.NotBad
  intro v
  have hv : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ (I.plc v).asIdeal := (I.pl v).2
  unfold GIdx at hg
  obtain ⟨hp, -, -, -, hlev, hT⟩ := hg
  have hne : ∀ i, ¬ D.what₂.places.resChar w ∣ D.host.g i := fun i hd => hlev (by
    rw [(Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime i)).mp hd]
    exact D.host.g_level i)
  exact ⟨natCast_notMem _ hp hv (hne 0), natCast_notMem _ hp hv (hne 1), natCast_notMem _ hp hv hT⟩

theorem isHyperbolicAt_rec_of_isSelfDualAt (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') (hs : Cmp.SelfDualAtP I) :
    Cmp.HypAtP I :=
  hypAtP_C I (notBad_C D u w hg I) hs

end Formalism.L2.G
