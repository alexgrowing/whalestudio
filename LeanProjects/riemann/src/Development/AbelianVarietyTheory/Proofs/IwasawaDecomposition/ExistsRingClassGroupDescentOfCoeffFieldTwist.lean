import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwistDescent

variable {D : D7} {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl}

abbrev rd (ρ : Reading i k b v) : D.ntw.Ok i k →+* FractionRing ρ.Oe :=
  (algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap (D.ntw.Ok i k) ρ.Oe)

theorem rd_injective (ρ : Reading i k b v) : Function.Injective (rd ρ) :=
  (IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj

theorem eq_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g g' : G D.host.E D.nd.Om) : χ g = χ g' ↔ ψ₀ g = ψ₀ g' := by
  constructor
  · intro he
    apply Units.ext
    apply ρ.emb.injective
    rw [h g, h g', he]
  · intro he
    apply Units.ext
    apply rd_injective ρ
    rw [← h g, ← h g', he]

theorem one_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g : G D.host.E D.nd.Om) : χ g = 1 ↔ ψ₀ g = 1 := by
  simpa using eq_iff_of_reads h g 1

theorem twOK_of_reads {ρ : Reading i k b v} {Q : Finset (PlE D.host)} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (hs : ∀ u ∈ Q, IsSplitPl D.host u) (hd : Disjoint Q (D.ntw.S0 i))
    (ho : IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om))) (ha : AntiHom D.ntw.cc ψ₀)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hr : RamExactly ψ₀ (↑Q : Set (PlE D.host)))
    (ht : BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i)) : IntegralHeckeForms.TwOK i k Q χ := by
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads h g
  refine ⟨hs, hd, hker ▸ ho, fun g g' hg => ?_, fun g => ?_, fun w A hA => ?_, fun w hw A hA σ hσ => ?_⟩
  · rw [← map_inv, eq_iff_of_reads h, map_inv]
    exact ha g g' hg
  · have h1 : χ g ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, one_iff_of_reads h, map_pow]
      exact hp g
    have h2 : ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨a, -, h3⟩ := (D.ntw.zk_prim i k).eq_pow_of_pow_eq_one h2
    refine Subgroup.mem_zpowers_iff.2 ⟨(a : ℤ), ?_⟩
    rw [zpow_natCast]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h3)
  · rw [← hr w A hA]
    simp only [ne_eq, one_iff_of_reads h]
  · exact (one_iff_of_reads h σ).2 (ht w hw A hA σ hσ)

theorem exists_reads {ρ : Reading i k b v} (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) :
    ∃ χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ, (∀ g, χ g ∈ Subgroup.zpowers (D.ntw.zk i k)) ∧
      ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) := by
  have hz : IsPrimitiveRoot (rd ρ (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) :=
    (D.ntw.zk_prim i k).map_of_injective (rd_injective ρ)
  have hx : ∀ g, ∃ a : ℕ, rd ρ (((D.ntw.zk i k) ^ a : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) =
      ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) := fun g => by
    have h1 : (ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL)) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp g, Units.val_one, map_one]
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one h1
    exact ⟨a, by rw [Units.val_pow_eq_pow_val, map_pow]; exact ha⟩
  choose a ha using hx
  let χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ := MonoidHom.mk' (fun g => D.ntw.zk i k ^ a g) fun g g' => by
    apply Units.ext
    apply rd_injective ρ
    rw [ha (g * g'), map_mul ψ₀, Units.val_mul, map_mul ρ.emb, Units.val_mul, map_mul (rd ρ), ha, ha]
  refine ⟨χ, fun g => ⟨(a g : ℤ), by simp [χ]⟩, fun g => (ha g).symm⟩

theorem exists_pulls_twOK : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v) (Q : Finset (PlE D.host)) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∀ u ∈ Q, IsSplitPl D.host u) → Disjoint Q (D.ntw.S0 i) → IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc ψ₀ → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → RamExactly ψ₀ (↑Q : Set (PlE D.host)) → BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i) → (∃ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀) ∧ ∀ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀ → IntegralHeckeForms.TwOK i k Q (ψ.comp (D.ntw.art i Q)) := by
  intro D i k b v ρ Q ψ₀ hs hd ho ha hp hr ht
  refine ⟨?_, fun ψ hψ => twOK_of_reads (ρ := ρ) (fun g => hψ g) hs hd ho ha hp hr ht⟩
  obtain ⟨χ, hv, hχ⟩ := exists_reads (ρ := ρ) ψ₀ hp
  have hfin : IsOfFinOrder (D.ntw.zk i k) := isOfFinOrder_iff_pow_eq_one.2
    ⟨_, pow_pos (D.ntw.lPrime i).out.pos k, (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one⟩
  haveI : Finite (Subgroup.zpowers (D.ntw.zk i k)) := (finite_zpowers.2 hfin).to_subtype
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads hχ g
  obtain ⟨f, hf⟩ := D.ntw.art_univ i Q
    (fun u hu hl => Finset.disjoint_left.1 hd hu (D.ntw.twistExcludedPlaces_contains_residueChar i hl)) (Subgroup.zpowers (D.ntw.zk i k))
    (by
      rintro ⟨x, n, rfl⟩
      refine ⟨k, Subtype.ext ?_⟩
      change (D.ntw.zk i k ^ n) ^ (D.ntw.l i ^ k) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one, one_zpow])
    (χ.codRestrict _ hv) (by rw [MonoidHom.ker_codRestrict, hker]; exact ho)
    (fun g g' h => Subtype.ext (by
      change χ g' = (χ g)⁻¹
      rw [← map_inv, eq_iff_of_reads hχ, map_inv]
      exact ha g g' h))
    (fun u hu A hA σ hσ => Subtype.ext (by
      change χ σ = 1
      rw [one_iff_of_reads hχ]
      by_contra hne
      exact hu ((hr u A hA).1 ⟨σ, hσ, hne⟩)))
  refine ⟨(Subgroup.zpowers (D.ntw.zk i k)).subtype.comp f, fun g => ?_⟩
  have h1 : f (D.ntw.art i Q g) = χ.codRestrict _ hv g := by rw [← hf]; rfl
  change ρ.emb _ = rd ρ (((f (D.ntw.art i Q g) : Subgroup.zpowers (D.ntw.zk i k)) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)
  rw [h1]
  exact hχ g

end GlobalTheory.TwistDescent
