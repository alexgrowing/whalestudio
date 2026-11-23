import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsForComponent
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem blkF_ne_inl (Ψ : Type) (p q : ℕ) {K₀ : Type} (k : K₀) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r ≠ some (.inl k) := by
  unfold blkF
  split_ifs <;> simp

theorem hasSncBoundary_reTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (ht : CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀))) (e : ℕ), HasSncBoundary 𝔐 e → HasSncBoundary (reTie 𝔐 (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) ht) e := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ ht e hs
  obtain ⟨bd, hsnc, hiff⟩ := hs
  let bk : K₀ → NonPluckerBlocks (blkF (CMType H) D.p D.q K₀) :=
    fun k => ⟨Sum.inl k, fun r => blkF_ne_inl (CMType H) D.p D.q k r⟩
  let bx : ∀ k, J₀ k ≃ baseIdx (idx (p := D.p) (q := D.q) J₀ n) (blkF (CMType H) D.p D.q K₀) (bk k) :=
    fun k => Equiv.refl _
  have hval : ∀ (k : K₀) (a : J₀ k),
      xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨bk k, bx k a⟩ = x₀ ⟨k, a⟩ := fun _ _ => rfl
  have hreg : ∀ q' : Cpt 𝔐.ξ, (∀ r : ℕ, Nat.Prime r → ¬ InFibre 𝔐.ξ r q') →
      ∀ h : genPt 𝔐.ξ ⤳ (𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q'.1, regAt 𝔐.ξ q' = regAt 𝔐.ξ ⟨(𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q'.1, h⟩ :=
    fun _ _ _ => rfl
  have hinj : ∀ q₁ q₂ : Cpt 𝔐.ξ, (∀ r : ℕ, Nat.Prime r → ¬ InFibre 𝔐.ξ r q₁) →
      (𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q₁.1 = (𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q₂.1 → q₁ = q₂ :=
    fun _ _ _ h => Subtype.ext h
  have hsnc' := GlobalTheory.CompanionTheory.Ar.SncRefine.isSncModel_refine 𝔐.X 𝔐.X Ω 𝔐.ξ 𝔐.ξ (𝟙 _) K₀ J₀ x₀ _ _
    (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) bk bx e bd 𝔐.all 𝔐.all 𝔐.tie ht (Category.comp_id _)
    hval hreg hinj hsnc
  unfold HasSncBoundary
  refine ⟨_, hsnc', fun z w hw => ?_⟩
  have hdown := GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down 𝔐.X 𝔐.X Ω 𝔐.ξ 𝔐.ξ (𝟙 _) K₀ J₀ x₀ _ _
    (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) bk bx z w 𝔐.all 𝔐.all 𝔐.tie.gen (Category.comp_id _) hval hreg hw
  have hnd1 : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
  have hnd2 : ∀ k, ∃ i, w ⟨bk k, bx k i⟩ ≠ 0 := fun k => (hdown.1 k).imp fun _ h => h.ne_zero
  exact (GlobalTheory.CompanionTheory.Ar.EigBase.mem_mcPts_rename (fun p => (⟨bk p.1, bx p.1 p.2⟩ : Σ k, _)) bd w hnd1 hnd2).trans
    (hiff z _ hdown)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
