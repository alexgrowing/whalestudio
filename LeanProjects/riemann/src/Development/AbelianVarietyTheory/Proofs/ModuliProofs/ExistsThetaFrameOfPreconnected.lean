import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreFrameOfMemClosure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ThetaFamily

theorem thetaChar_family {g m : ℕ} {B : Set (Fin m → ℂ)} {p q : Fin g → (Fin m → ℂ) → (Fin g → ℂ)}
    {h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hp : ∀ k, DifferentiableOn ℂ (p k) B)
    (hq : ∀ k, DifferentiableOn ℂ (q k) B)
    (hh : ∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (p k b) = Pi.single k 1 ∧
      (h b).mulVec (q k b) = (τ b).mulVec (Pi.single k 1))
    {c₁ c₂ : Fin g → ℂ} (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) :
    DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ ((h bz.1).mulVec bz.2))
      (B ×ˢ Set.univ) ∧ ∀ b ∈ B, ∀ z, ∃ᶠ w in nhds z, thetaChar (τ b) c₁ c₂ ((h b).mulVec w) ≠ 0 := by
  have re : ∀ {c : Fin g → ℂ}, (∀ k, c k = 0 ∨ c k = 1 / 2) → ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := fun {c} hc =>
    ⟨fun i => (c i).re, funext fun i => by rcases hc i with e | e <;> simp [e]⟩
  obtain ⟨a₁, rfl⟩ := re h₁
  obtain ⟨a₂, rfl⟩ := re h₂
  have hinv : ∀ b ∈ B, h b * Matrix.of (fun i k => p k b i) = 1 := fun b hb => by
    ext i k
    have := congrFun ((hh b hb).2 k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  have dh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B :=
    differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hp k) i) hinv
  have dτ : ∀ i k, DifferentiableOn ℂ (fun b => τ b i k) B := fun i k => by
    refine (DifferentiableOn.fun_sum (u := Finset.univ) fun j _ =>
      (dh i j).mul (differentiableOn_pi.1 (hq k) j)).congr fun b hb => ?_
    have := congrFun ((hh b hb).2 k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this.symm
  have fst : ∀ {f : (Fin m → ℂ) → ℂ}, DifferentiableOn ℂ f B →
      DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => f bz.1) (B ×ˢ Set.univ) := fun hf =>
    hf.comp differentiableOn_fst fun _ h => h.1
  refine ⟨CanTh.differentiableOn_thetaChar (T := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => τ bz.1)
    (Z := fun bz => (h bz.1).mulVec bz.2) (fun i k => fst (dτ i k)) (differentiableOn_pi.2 fun i => ?_)
    (fun w hw => CanTh.mem_thetaDomain (hh _ hw.1).1) a₁ a₂, fun b hb => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun j _ => (fst (dh i j)).mul (by fun_prop)
  · have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b).mulVec w) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b))).differentiable
    refine frequently_ne_zero_of_entire
      (θ := fun w => thetaChar (τ b) (fun i => (a₁ i : ℂ)) (fun i => (a₂ i : ℂ)) ((h b).mulVec w))
      ((CanTh.differentiable_thetaChar (CanTh.mem_thetaDomain (hh b hb).1) a₁ a₂).comp dl) fun h0 => ?_
    refine thetaChar_ne_zero (hh b hb).1 a₁ a₂ (funext fun w => ?_)
    have := congrFun h0 ((Matrix.of (fun i k => p k b i)).mulVec w)
    rwa [Matrix.mulVec_mulVec, hinv b hb, Matrix.one_mulVec] at this

theorem exists_thetaFrame_of_preconnected : Out.Laws → (∀ (k : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶
    Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g →
    ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g →
    ℂ), ∃ c₁ c₂, cc = (c₁,
    c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z))) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (x : X), ∃ (V : X.Opens) (θ
    : ∀ i, Γ(P.A.left, P.A.hom ⁻¹ᵁ V ⊓ P.L.U i)), x ∈ V ∧ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ
    V) ∧ (∀ y ∈ V, ∃ (a : P.A.left) (i : P.L.ι), P.A.hom a = y ∧ a ∈ P.A.left.basicOpen (θ
    i))) → (∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ
    V] [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V')) (f θ F
    : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W → (∀ w ∈ W, F w * θ w = f w) → (∀ b, DifferentiableOn ℂ (fun z => F (b,
    z)) {z | (b, z) ∈ W}) → (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1,
    z) ≠ 0) → DifferentiableOn ℂ F W) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D'
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+
    (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m →
    ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧
    ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ
    (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧
    (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a
    : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k
    1)) → IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P → IsHolTo B y → IsHolTo (B ×ˢ
    Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1
    bz.2).left) → ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP B y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) := by
  intro laws hsm hobj hpt hsec _ E _ _ _ H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh _ hc hP hy hol
  have pt := hpt E H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh
  have th := fun (c₁ c₂ : Fin g → ℂ) h₁ h₂ => thetaChar_family (c₁ := c₁) (c₂ := c₂)
    (p := fun k b => P b (bas (Pi.single (.inl k) 1))) (q := fun k b => P b (bas (Pi.single (.inr k) 1)))
    (fun k => hP.2 _) (fun k => hP.2 _) hh h₁ h₂
  have he : ∀ b ∈ B, ∀ z, (e b z).left ≫ Xo.univ.t.G.hom = y b := fun b _ z => Over.w (e b z)
  have he0 : ∀ b ∈ B, (e b 0).left = y b ≫ eSec Xo.univ.t.G := fun b hb => by
    rw [((hU b hb).2.2.2.1 0).2 (zero_mem _)]
    rfl
  have := Xo.smooth
  have := (hsm _ _ Xo.s (SmoothOfRelativeDimension.smooth D.dim Xo.s)).2.2
  obtain ⟨o₁, o₂, o₃, o₄⟩ := hobj E H D l _ _ _ _ Xo.univ
  have sec : ∀ b₀ ∈ B, ∃ (V : Xo.X.Opens) (θ₀ : ∀ j, Γ(Xo.univ.t.G.left, Xo.univ.t.G.hom ⁻¹ᵁ V ⊓ Xo.univ.t.PP.L.U j)),
      ⊤ ≤ y b₀ ⁻¹ᵁ V ∧ ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre Xo.univ.t.PP (y b) V θ₀ := fun b₀ _ => by
    obtain ⟨V, θ₀, m₀, s₀, n₀⟩ := hsec Xo.X
      { A := Xo.univ.t.G, isAb := o₁, g := _, smoothDim := o₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB
        rigid := o₃, sym := o₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv } (y b₀ (default : PrimeSpectrum ℂ))
    exact ⟨V, θ₀, (top_le_preimage_iff_mem _ _).2 m₀, fun b _ hb =>
      exists_ratio_fibre laws.globalSectionsRank Xo.univ (y b) V θ₀ s₀ n₀ hb⟩
  choose! c hc₁ hc₂ using pt
  let C₀ : Set (Fin g → ℂ) := Set.pi Set.univ fun _ => {0, 1 / 2}
  have fin : (C₀ ×ˢ C₀).Finite := (Set.Finite.pi fun _ => Set.toFinite _).prod (Set.Finite.pi fun _ => Set.toFinite _)
  have hc₃ : ∀ b ∈ B, (∀ k, (c b).1 k = 0 ∨ (c b).1 k = 1 / 2) ∧ (∀ k, (c b).2 k = 0 ∨ (c b).2 k = 1 / 2) ∧
      ∃ fr, IsFibreFrame Xo.univ.t.PP (y b) (fun z => (e b z).left)
        (fun z => thetaChar (τ b) (c b).1 (c b).2 ((h b).mulVec z)) fr := fun b hb => by
    obtain ⟨c₁, c₂, e₀, r₁, r₂, r₃⟩ := hc₁ b hb
    have r := isThetaFrame_singleton_iff.1 r₃
    rw [e₀]
    exact ⟨r₁, r₂, r⟩
  have const := eq_of_finite_of_closed_fibres hc fin c
    (fun b hb => ⟨fun k _ => (hc₃ b hb).1 k, fun k _ => (hc₃ b hb).2.1 k⟩) (fun k hk b hb hcl => by
      have k₁ := fun i => hk.1 i trivial
      have k₂ := fun i => hk.2 i trivial
      obtain ⟨V, θ₀, hV₀, hV⟩ := sec b hb
      obtain ⟨fr', h'⟩ := (hc₃ b hb).2.2
      have r := exists_fibreFrame_of_mem_closure (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 hb hV₀ hV
        (T := {b' ∈ B | c b' = k}) (fun b' hb' => by have r := (hc₃ b' hb'.1).2.2; rw [hb'.2] at r; exact r) hcl
        ((th _ _ (hc₃ b hb).1 (hc₃ b hb).2.1).2 b hb) h'
      exact (hc₂ b hb k ⟨k.1, k.2, rfl, k₁, k₂, (isThetaFrame_singleton_iff (y := y) (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z))).2 r⟩).symm)
  obtain ⟨k, k₁, k₂, hk⟩ : ∃ k : (Fin g → ℂ) × (Fin g → ℂ), (∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2) ∧
      (∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2) ∧ ∀ b ∈ B, c b = k := by
    rcases B.eq_empty_or_nonempty with h0 | ⟨b₀, hb₀⟩
    · exact ⟨0, fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun b hb => absurd (h0 ▸ hb) (Set.notMem_empty b)⟩
    · exact ⟨c b₀, (hc₃ b₀ hb₀).1, (hc₃ b₀ hb₀).2.1, fun b hb => const b hb b₀ hb₀⟩
  exact ⟨k.1, k.2, k₁, k₂, isThetaFrame_of_fibreFrames (e := fun b z => (e b z).left)
    (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he he0 hy hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 sec
    fun b hb => by have r := (hc₃ b hb).2.2; rw [hk b hb] at r; exact r⟩

end GlobalTheory.ThetaFamily
