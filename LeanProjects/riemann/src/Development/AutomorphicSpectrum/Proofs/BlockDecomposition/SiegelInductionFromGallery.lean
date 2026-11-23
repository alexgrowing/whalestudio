import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

noncomputable section

open PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

section Heights

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isHt_mono {Γ K P P' : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) (hP : P' ≤ P) : IsHt Γ K P' η :=
  ⟨fun p hp g => h.left p (hP hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hP hp), h.cont⟩

theorem isHt_lin {Γ K P : Subgroup G} {η θ : G → ℝ} (x y : ℝ) (h₁ : IsHt Γ K P η) (h₂ : IsHt Γ K P θ) :
    IsHt Γ K P fun g => x * η g + y * θ g where
  left p hp g := by simp only [h₁.left p hp g, h₂.left p hp g]; ring
  right g k hk := by simp only [h₁.right g k hk, h₂.right g k hk]
  rat γ hγ hp := by simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp]; ring
  cont := (continuous_const.mul h₁.cont).add (continuous_const.mul h₂.cont)

theorem isHt_congr {Γ K P : Subgroup G} {η θ : G → ℝ} (h : IsHt Γ K P η) (e : ∀ g, θ g = η g) : IsHt Γ K P θ := by
  rwa [show θ = η from funext e]

theorem conv_congr {Γ P : Subgroup G} {l l' : G → ℝ} (h : Conv Γ P l) (e : ∀ g, l' g = l g) : Conv Γ P l' := by
  rwa [show l' = l from funext e]

end Heights

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]

open Classical in

theorem wallQ (hTr : Transfer) (hTop : GrpTop) (hPar : ParLaw) (hLQ : LeviQ) (A : Ad E R) (hA : A.Good) (ε : ℤˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Set ι) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι))
    (hSg : A.Sg ε (sᶜ : Set ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasWall (A.uΓ ε ι ⊓ A.uQ ε s) (A.uK ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uC ε ι)
      (fun g => A.uH ε Set.univ g - A.uH ε s g) (fun g => A.uH ε Set.univ g - A.uH ε s g)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g)) ρ := by
  obtain ⟨π, j, c₀, hL, hP, hIw, hPH⟩ := hLQ E R A hA ι ε s hI
  obtain ⟨-, -, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨-, -, -, u₄, u₅, -, u₇⟩ := hTop E R A hA (sᶜ : Set ι) ε
  have hP' := (hPar E R A hA (sᶜ : Set ι) ε Set.univ).2 (by rwa [inf_idem])
  rw [inf_idem] at hP'
  obtain ⟨hp, hh, -⟩ := hP'
  have hβ' : IsHt (A.uΓ ε (sᶜ : Set ι)) (A.uK ε (sᶜ : Set ι)) (A.uQ ε Set.univ)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card (sᶜ : Set ι) : ℝ) 0 hh hh) fun g => by ring
  have hPβ : PullHt (A.uK ε ι) (A.uQ ε s) π
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g))
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) := by
    intro q k hk
    have := hPH q k hk
    simp only at this ⊢
    rw [this]
  exact (hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j c₀ _ _ _ _ _ _ _ _ _ _ 0 u₇ hL hP hP hP hp hp hp hh hh hβ'
    hPH hPH hPβ hPH).1 (hSg hIw)

theorem wallsS (hTr : Transfer) (hTw : Twist) (hTop : GrpTop) (hPar : ParLaw) (hLS : LeviS) (A : Ad E R) (hA : A.Good)
    (hMir : A.MirGL) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι) (hN : 2 ≤ Fintype.card ι)
    (hS : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasFirst (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)) ρ ∧
    HasWall (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uC ε ι) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g) (A.uH ε {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g) ρ ∧
    HasLast (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (A.uH ε Set.univ) (Fintype.card ι) ρ := by
  obtain ⟨π, j, hL, hP, -, hH⟩ := hLS E R A hA ι ε hS
  obtain ⟨g₁, g₂, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  have hk := hA.kcpt ι
  obtain ⟨a₁, a₂, ch, h₀, -⟩ := (hPar E R A hA ι ε {i₀}).1
  obtain ⟨b₁, b₂, -, h₁, -⟩ := (hPar E R A hA ι ε {i₁}ᶜ).1
  obtain ⟨u₁, u₂, -, hu, hst⟩ := (hPar E R A hA ι ε Set.univ).1
  rw [hst] at u₁ u₂ hu
  have hPS : IsPull (A.uQ ε Set.univ) (A.uQ ε Set.univ) ⊤ π 1 (A.uC ε ι) (A.cGL ι) := by
    have := hP Set.univ
    rwa [inf_idem, hst] at this
  have e : (1 : GL ι R → ℂ) * A.cGL ι = A.cGL ι := one_mul _
  obtain ⟨m₁, m₂, m₃⟩ := hMir ι i₀ i₁ hN
  have d₁ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin 1 (-1) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₂ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ)
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (1 - (Fintype.card ι : ℝ)) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₃ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (-1) h₀ (isHt_mono hu le_top)) fun g => by ring
  have p₁ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₂ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₃ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g)
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₀} q k hk', hH Set.univ q k hk']
  have T₁ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₀}) (stab R {i₁}ᶜ) 1 (A.cGL ι) (A.htGL {i₀})
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g)
    (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ a₁ b₁
  have T₂ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₁}ᶜ) (stab R {i₀}) 1 (A.cGL ι)
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
    (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ b₁ a₁
  rw [e] at T₁ T₂
  have X₁ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₀}) (hP {i₁}ᶜ) u₂ a₂ b₂ h₀ d₁ d₂ (hH {i₀}) p₁ p₂ (hH Set.univ)
  have X₂ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₁}ᶜ) (hP {i₀}) u₂ b₂ a₂ d₁ h₀ d₃ p₁ (hH {i₀}) p₃ (hH Set.univ)
  exact ⟨X₁.2.1 (T₁.2.1 m₁), X₂.1 (T₂.1 m₂), X₁.2.2 (T₁.2.2 m₃)⟩

open Classical in

theorem sgStep : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := by
  intro hGal hTr hTw hTop hPar hLS hLQ hCG hCU E R _ _ _ _ _ _ _ A hA hMir ε ι _ _ hN hIH hS W _ _ _ ρ hρ
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨π, j, -, -, hIw, -⟩ := hLS E R A hA ι ε hS
  obtain ⟨-, -, -, t₄, t₅, t₆, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨Ra, ca₁, ca₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀} (hIw _)
  obtain ⟨Rb, -, cb₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀}ᶜ (hIw _)
  have pS := (hPar E R A hA ι ε Set.univ).2 (hIw _)
  rw [inf_idem] at pS
  have pA := (hPar E R A hA ι ε {i₀}).2 (hIw _)
  have pB := (hPar E R A hA ι ε {i₀}ᶜ).2 (hIw _)
  have hc₀ : ∀ f : Fintype ({i₀}ᶜ : Set ι), @Fintype.card _ f = Fintype.card ι - 1 := fun f => by
    rw [Fintype.card_compl_set]; simp
  have hc₁ : ∀ f : Fintype (({i₀}ᶜ : Set ι)ᶜ : Set ι), @Fintype.card _ f = 1 := fun f => by
    rw [Fintype.card_compl_set, hc₀]; omega
  have hc₀' : ∀ f : Fintype ({i₀}ᶜ : Set ι), ((@Fintype.card _ f : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := fun f => by
    rw [hc₀, Nat.cast_sub (by omega)]; simp
  have hq := fun (s : Set ι) (f : Fintype (sᶜ : Set ι)) (d : DecidableEq (sᶜ : Set ι)) => @hIH (sᶜ : Set ι) f d
  have w₁ := wallQ hTr hTop hPar hLQ A hA ε {i₀} (hIw _)
    (hq _ _ _ (by rw [hc₀]; omega) (by rw [hc₀]; omega)) ρ hρ
  have w₂ := wallQ hTr hTop hPar hLQ A hA ε {i₀}ᶜ (hIw _)
    (hq _ _ _ (hc₁ _).ge (by rw [hc₁]; omega)) ρ hρ
  rw [hc₀'] at w₁
  rw [hc₁] at w₂
  simp only [Nat.cast_one, one_mul] at w₂
  rw [show (fun g => A.uH ε Set.univ g - A.uH ε {i₀}ᶜ g) = fun g => -(A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) from
    funext fun g => by ring] at w₂
  obtain ⟨s₁, s₂, s₃⟩ := wallsS hTr hTw hTop hPar hLS A hA hMir ε i₀ i₀ hN hS ρ hρ
  refine hGal (A.U ε ι) W (A.uK ε ι) ρ t₇ hρ inferInstance (A.uΓ ε ι) (A.uQ ε Set.univ)
    (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}) (A.uQ ε {i₀}ᶜ) (A.uC ε ι)
    (A.uH ε Set.univ) (A.uH ε {i₀}) (fun g => A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) (Fintype.card ι)
    inf_le_right inf_le_right inf_le_left inf_le_left pS.1 pA.1 pB.1 pS.2.1 pA.2.1
    (isHt_congr pB.2.1 fun g => by ring) ⟨max Ra Rb, fun y hy => ca₁ y (lt_of_le_of_lt (le_max_left _ _) hy),
      fun z y hz hy => ca₂ z y (lt_of_le_of_lt (le_max_left _ _) hz) (lt_of_le_of_lt (le_max_left _ _) hy),
      fun r y hr hy => conv_congr (cb₂ r y (lt_of_le_of_lt (le_max_right _ _) hr)
        (lt_of_le_of_lt (le_max_right _ _) hy)) fun g => by ring⟩ s₁ w₂ s₂ w₁ s₃

end GlobalTheory.CompanionTheory.RgEis
