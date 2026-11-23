import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateSpectral.HTSpecGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst
open UpperTheory.Gal.Int.Geo GlobalTheory.WeilDeligne GlobalTheory.HeckeGal

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

section Low
variable {k L : Type} [Field k] [Field L] {H : HTower k} {θ : H.Γ → L} {O : Type} [CommRing O] [Algebra O k]

structure LowData (C : Cover H θ O) : Type 1 where
  T : H.Γ → Scheme.{0}
  s : ∀ g, T g ⟶ C.Y
  t : ∀ g, T g ⟶ C.Y
  d : H.Γ → ℕ
  m : H.Γ → ℕ
  fet : ∀ g, FEt (s g) (d g)
  comm : ∀ g, t g ≫ C.p = s g ≫ C.p
  lies : ∀ g, C.Lies g (s g) (t g) (m g)

theorem lowData_ex (C : Cover H θ O) (h : C.Good) : Nonempty (LowData C) := by
  choose T s t d m h1 h2 h3 using h
  exact ⟨⟨T, s, t, d, m, h1, h2, h3⟩⟩

def low {C : Cover H θ O} (D : LowData C) : HTower k where
  Γ := H.Γ
  Z := pullback C.p (gen O k)
  q := pullback.snd _ _
  Y g := pullback (D.s g ≫ C.p) (gen O k)
  s g := pullback.lift (pullback.fst _ _ ≫ D.s g) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  t g := pullback.lift (pullback.fst _ _ ≫ D.t g) (pullback.snd _ _) (by rw [Category.assoc, D.comm, pullback.condition])
  comm g := by rw [pullback.lift_snd, pullback.lift_snd]

end Low

def LowNice : Prop := ∀ (k L : Type) [Field k] [Field L] (H : HTower k) (θ : H.Γ → L) (O : Type) [CommRing O] [Algebra O k]
  (C : Cover H θ O) (D : LowData C), Nice (low D)

def LowHodge : Prop := ∀ (k L F : Type) [Field k] [Field L] [Field F] [CharZero F] (φ : k →+* F) (ψ : L →+* F) (H : HTower k)
  (θ : H.Γ → L) (O : Type) [CommRing O] [Algebra O k] (C : Cover H θ O) (D : LowData C), Nice H → C.Onto → ∀ a : ℕ,
  HOcc (bcAlong H φ) (fun g => ψ (θ g)) a → HOcc (bcAlong (low D) φ) (fun g => ψ (θ g / D.m g)) a

def LowPiece : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
  (H : HTower E) (θ : H.Γ → Qbar l) (O : Type) [CommRing O] [Algebra O E] (C : Cover H θ O) (D : LowData C), Nice H → C.Onto →
  ∀ (d₁ d₀ : ℕ) (ρ₁ : (Ω ≃ₐ[E] Ω) →* GL (Fin d₁) (Qbar l)) (ρ₀ : (Ω ≃ₐ[E] Ω) →* GL (Fin d₀) (Qbar l)),
    IsMat l (low D) Ω (Qbar l) (fun g => θ g / D.m g) ρ₁ → IsMat l H Ω (Qbar l) θ ρ₀ →
    ∃ A : Matrix (Fin d₀) (Fin d₁) (Qbar l), Function.Injective A.mulVec ∧ ∀ σ, (ρ₀ σ).val * A = A * (ρ₁ σ).val

def MatEx : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
  (H : HTower E) (θ : H.Γ → Qbar l), Nice H → ∃ (d : ℕ) (ρ : (Ω ≃ₐ[E] Ω) →* GL (Fin d) (Qbar l)), IsMat l H Ω (Qbar l) θ ρ

def IsMatF {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω] (θ : H.Γ → Qbar l) {d : ℕ}
    (ρ : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Qbar l)) : Prop :=
  ∃ b : Module.Basis (Fin d) (Qbar l) (piece l H Ω (Qbar l) θ), ∀ σ j, galV l H Ω (Qbar l) σ (b j).1 = ∑ i, ρ σ i j • (b i).1

def LocalMat : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
  (H : HTower E) (θ : H.Γ → Qbar l), Nice H →
  ∀ (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (τK : E →+* ↥Bw.Kw.1), (∀ x, (τK x : Qbar l) = Bw.j (algebraMap E Ω x)) →
    HasOps l (bcAlong H τK) (Qbar l) id ∧ ∀ (d : ℕ) (ρ : (Ω ≃ₐ[E] Ω) →* GL (Fin d) (Qbar l)), IsMat l H Ω (Qbar l) θ ρ →
      IsMatF (bcAlong H τK) (Qbar l) θ fun σ => (ρ (Bw.e.symm ((IntermediateField.fixingSubgroupEquiv Bw.Kw.1).symm σ) : Gw)).val

def CoverLow : Prop := CrystallineSemistableComparison.HTSpecB.HTSpecGood →
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (H : HTower E) (θ : H.Γ → Qbar l) (w : HeightOneSpectrum (𝓞 E))
    (C : Cover H θ (Ow w)) (D : LowData C) (K : FinExt l) (τK : E →+* ↥K.1),
    (∀ x : Ow w, ‖(τK (x : E) : Qbar l)‖ ≤ 1) → ∀ n, HTCover (bcAlong (low D) τK) id n

def BridgeInt : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
  (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
  ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
  ∀ (γ : GQ l) (x : Ow w), ‖γ (Bw.j (algebraMap E Ω (x : E)))‖ ≤ 1

def BCTower : Prop := ∀ (k K F : Type) [Field k] [Field K] [Field F] (τ : k →+* K) (φ : K →+* F) (H : HTower k), Nice H →
  Nice (bcAlong H τ) ∧ Nonempty (TowerBC φ (bcAlong H τ) (bcAlong H (φ.comp τ)) id id)

def LocE : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ιC : Qbar l ≃+* ℂ) (H : HTower ↥K.1) (H' : HTower ℂ) (ι' : H.Γ → H'.Γ)
    (_ : TowerBC (ιC.toRingHom.comp (algebraMap ↥K.1 (Qbar l))) H H' id ι') (θ : H.Γ → Qbar l) (θ' : H'.Γ → ℂ) (a : ℕ),
    (∀ g, θ' (ι' g) = ιC (θ g)) → Nice H → HasOps l H (Qbar l) id → (∀ n, HTCover H id n) → HOcc H' θ' a →
    ∀ (d : ℕ) (ρ : (Qbar l ≃ₐ[↥K.1] Qbar l) → Matrix (Fin d) (Fin d) (Qbar l)), IsMatF H (Qbar l) θ ρ →
      HTOcc (K := K) (fun σ => ρ (IntermediateField.fixingSubgroupEquiv K.1 σ)) a

def LocEOf : Prop := HodgeBC → TraceSplit → CoverOp → LocE

def OccMove : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (a : ℤ),
  (∀ (d₁ d₀ : ℕ) (ρ₁ : ↥(GK K) → Matrix (Fin d₁) (Fin d₁) (Qbar l)) (ρ₀ : ↥(GK K) → Matrix (Fin d₀) (Fin d₀) (Qbar l))
    (A : Matrix (Fin d₀) (Fin d₁) (Qbar l)), Function.Injective A.mulVec → (∀ σ, ρ₀ σ * A = A * ρ₁ σ) → HTOcc ρ₁ a → HTOcc ρ₀ a) ∧
  ∀ (d : ℕ) (ρ₀ ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (Qbar l)) (c : Fin d → ℕ),
    (∀ σ, (ρ₀ σ).BlockTriangular c ∧ ∀ i j, ρ σ i j = if c i = c j then ρ₀ σ i j else 0) → HTOcc ρ₀ a → HTOcc ρ a

def JumpsEx : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
  (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
  ∀ (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (d : ℕ) (r : ↥Gw →* GL (Fin d) (Qbar l)), IsCrysAt P Bw r →
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∃ J, IsJumpsAt P Bw r τ J

def JumpCore : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (H : HTower E) (θ : H.Γ → Qbar l), Nice H → ∀ (dd : ℕ) (ρ₀ ρ : (Ω ≃ₐ[E] Ω) →* GL (Fin dd) (Qbar l)),
    IsMat l H Ω (Qbar l) θ ρ₀ → IsGr ρ₀ ρ → ∀ w : HeightOneSpectrum (𝓞 E), GoodAt H θ w →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
      IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) →
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∃ J : Multiset ℤ, IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J ∧
          ∀ b : ℕ, HOcc (bcAlong H (ι.toRingHom.comp τ)) (fun g => ι (θ g)) b → (b : ℤ) ∈ J

theorem jumpStep_of (hJ : JumpCore) (hC : CrysStep) : JumpStep := by
  intro E Ω _ _ _ _ _ l _ ι H θ hN dd ρ hc hP w hw hG P AI hT A hA O _ _ _ Bw hj τ LL' τ' hτ
  obtain ⟨ρ₀, hM, hGr⟩ := id hP
  obtain ⟨C, hO, -⟩ := id hG
  obtain ⟨J, h1, h2⟩ := hJ E Ω l ι H θ hN dd ρ₀ ρ hM hGr w hG P AI hT A hA O Bw hj
    (hC E Ω l H θ hN dd ρ hc hP w hw C hO P AI hT A hA O Bw hj) τ LL' τ' hτ
  exact ⟨J, h1, fun j ⟨b, hb, ho⟩ => hb ▸ h2 b ho⟩

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
