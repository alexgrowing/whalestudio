import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

private theorem UpperTheory.exists_linear_lift_of_labels {Λ La T M : Type} [CommRing Λ] [AddCommGroup La] [Module Λ La]
    [Module.Projective Λ La] [AddCommGroup T] [Module Λ T] [CommGroup M] (l : T → M) (act : Λ → M → M)
    (lb : La → M) (hl : ∀ s t, l (s + t) = l s * l t) (hla : ∀ (o : Λ) t, l (o • t) = act o (l t))
    (hb : ∀ a b, lb (a + b) = lb a * lb b) (hba : ∀ (o : Λ) a, lb (o • a) = act o (lb a))
    (hs : ∀ a, ∃ t, l t = lb a) : ∃ f : La →ₗ[Λ] T, ∀ a, l (f a) = lb a := by
  let Q : Submodule Λ (La × T) :=
    { carrier := {x | l x.2 = lb x.1}
      add_mem' := fun {x y} hx hy => by
        change l (x.2 + y.2) = lb (x.1 + y.1)
        rw [hl, hb, show l x.2 = lb x.1 from hx, show l y.2 = lb y.1 from hy]
      zero_mem' := by
        change l 0 = lb 0
        have h1 := hl 0 0
        have h2 := hb 0 0
        rw [add_zero] at h1 h2
        rw [left_eq_mul.1 h1, left_eq_mul.1 h2]
      smul_mem' := fun o x hx => by
        change l (o • x.2) = lb (o • x.1)
        rw [hla, hba, show l x.2 = lb x.1 from hx] }
  obtain ⟨h, hh⟩ := Module.projective_lifting_property ((LinearMap.fst Λ La T) ∘ₗ Q.subtype) LinearMap.id
    (fun a => by
      obtain ⟨t, ht⟩ := hs a
      exact ⟨⟨(a, t), ht⟩, rfl⟩)
  refine ⟨(LinearMap.snd Λ La T) ∘ₗ Q.subtype ∘ₗ h, fun a => ?_⟩
  have h1 : (h a).1.1 = a := LinearMap.congr_fun hh a
  have h2 : l (h a).1.2 = lb (h a).1.1 := (h a).2
  rw [h1] at h2
  exact h2

theorem UpperTheory.weil_pairing_labels_torsion_points :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P : PtP E p) (lb : Dw.La → GlobalTheory.ChTor.Pts P.A.A) (ζ : ℂ_[p]ˣ), 1 ≤ n → IsPrimitiveRoot ζ (p ^ n) → (∀ a b, lb (a + b) = lb a * lb b) → (∀ (o : 𝓞 E) a, lb (o • a) = lb a ≫ P.oA.act o) → (∀ σ : GlobalTheory.ChTor.Pts P.A.A, σ ^ (p ^ n) = 1 ↔ ∃ a, lb a = σ) → (∀ a b, weil P.A (p ^ n) (lb a) (lb b) = ζ ^ Dw.EF a b) → ∃ (f : Dw.La →+ P.T) (u : ℤ_[p]), (∀ a, (f a).lev n = lb a) ∧ (∀ (o : 𝓞 E) a, f (o • a) = P.actT o (f a)) ∧ IsUnit u ∧ ∀ a b, (p : ℤ_[p]) ^ n ∣ pairT P.A P.eps (f a) (f b) - u * (Dw.EF a b : ℤ_[p]) := by
  intro E _ _ _ H Dw p _ n _ P lb ζ hn hζ hadd hact htor hweil
  have hp : p.Prime := Fact.out
  haveI := Dw.proj
  letI : Module (𝓞 E) P.T := Module.compHom P.T P.actT
  obtain ⟨f, hf⟩ := UpperTheory.exists_linear_lift_of_labels (Λ := 𝓞 E) (La := Dw.La) (T := P.T) (fun t => t.lev n)
    (fun o x => x ≫ P.oA.act o) lb (fun _ _ => rfl) (fun _ _ => rfl) hadd hact
    (fun a => (tate_free_of_card p _ _ P.card_torsion).2.1 n _ ((htor _).2 ⟨a, rfl⟩))
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hε := P.eps.isPrimitiveRoot n
  obtain ⟨k, -, hk⟩ := hε.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).2 hζ.pow_eq_one)
  have hcop : k.Coprime (p ^ n) := (hε.pow_iff_coprime (pow_pos hp.pos n) k).1 (hk ▸ hζ)
  refine ⟨f.toAddMonoidHom, (k : ℤ_[p]), hf, fun o a => f.map_smul o a, ?_, fun a b => ?_⟩
  · rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hcop).symm
  · have h1 := pow_pairT P.A P.eps (f a) (f b) n
    have hfa : (f a).lev n = lb a := hf a
    have hfb : (f b).lev n = lb b := hf b
    rw [hfa, hfb, hweil, ← hk] at h1
    change _ ∣ pairT P.A P.eps (f a) (f b) - _
    generalize pairT P.A P.eps (f a) (f b) = x at h1 ⊢
    have h2 : P.eps.1.lev n ^ ((GlobalTheory.PDiv.digit n x : ℤ) - k * Dw.EF a b) = 1 := by
      rw [zpow_sub, zpow_natCast, h1, zpow_mul, zpow_natCast, mul_inv_cancel]
    obtain ⟨c, hc⟩ := (hε.zpow_eq_one_iff_dvd _).1 h2
    have h3 := congrArg (Int.cast : ℤ → ℤ_[p]) hc
    push_cast at h3
    obtain ⟨d, hd⟩ := GlobalTheory.PDiv.pow_dvd_sub_digit n x
    exact ⟨d + c, by linear_combination hd + h3⟩
