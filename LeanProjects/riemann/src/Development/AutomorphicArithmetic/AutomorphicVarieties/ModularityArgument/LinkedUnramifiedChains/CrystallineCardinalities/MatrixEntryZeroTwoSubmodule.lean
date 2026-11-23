import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.HomBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.HomMuLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J.YEx

private def matrixEntryZeroTwoSubmodule (R : Type) [CommRing R] : Submodule ℤ (Matrix (Fin 3) (Fin 3) R) where
  carrier := {X | ∀ a b, ¬ (a = 0 ∧ b = 2) → X a b = 0}
  add_mem' := fun hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

private theorem single_mem {R : Type} [CommRing R] (x : R) : Matrix.single (0 : Fin 3) (2 : Fin 3) x ∈ matrixEntryZeroTwoSubmodule R := by
  intro a b h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨rfl, rfl⟩

private theorem eq_single {R : Type} [CommRing R] {X : Matrix (Fin 3) (Fin 3) R} (h : X ∈ matrixEntryZeroTwoSubmodule R) :
    X = Matrix.single (0 : Fin 3) (2 : Fin 3) (X 0 2) := by
  ext a b
  rw [Matrix.single_apply]
  by_cases hab : a = 0 ∧ b = 2
  · obtain ⟨rfl, rfl⟩ := hab
    simp
  · rw [if_neg (fun h' => hab ⟨h'.1.symm, h'.2.symm⟩)]
    exact h a b hab

private def e02 (R : Type) [CommRing R] : R ≃+ matrixEntryZeroTwoSubmodule R where
  toFun x := ⟨Matrix.single 0 2 x, single_mem x⟩
  invFun X := X.1 0 2
  left_inv x := by simp
  right_inv X := Subtype.ext (eq_single X.2).symm
  map_add' x y := Subtype.ext (by simp [Matrix.single_add])

private def zM {R : Type} [CommRing R] (i : Fin 2) (u b : R) : Matrix (Fin 3) (Fin 3) R :=
  if i = 0 then !![u, b, 0; 0, 0, 0; 0, 0, 0] else !![0, 0, 0; 0, 0, b; 0, 0, -u]

private theorem zM_upT {R : Type} [CommRing R] (i : Fin 2) (u b : R) : UpT (zM i u b) := by
  intro a c h
  fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h ⊢

private theorem zM_diag {R : Type} [CommRing R] (i : Fin 2) (b : R) (j : Fin 3) : zM i 0 b j j = 0 := by
  fin_cases i <;> fin_cases j <;> simp [zM]

private theorem zM_diff {R : Type} [CommRing R] (i : Fin 2) (u b : R) :
    zM i u b i.castSucc i.castSucc - zM i u b i.succ i.succ = u := by
  fin_cases i <;> simp [zM]

private theorem zM_coc {O R : Type} [CommRing O] [CommRing R] [Module O R] (i : Fin 2) (u b u' b' b'' : R)
    (Y : Matrix (Fin 3) (Fin 3) R) (p q : Fin 2 → O) (h1 : UpT Y) (h2 : ∀ j, Y j j = zM i u' b' j j)
    (h3 : ∀ j : Fin 2, Y j.castSucc j.succ = p j • zM i u' b' j.castSucc j.succ -
      q j • (zM i u' b' j.castSucc j.castSucc - zM i u' b' j.succ j.succ))
    (h4 : b'' = b + p i • b' - q i • u') : zM i (u + u') b'' - zM i u b - Y ∈ matrixEntryZeroTwoSubmodule R := by
  subst h4
  intro a c h
  have d0 := h2 0
  have d1 := h2 1
  have d2 := h2 2
  have s0 := h3 0
  have s1 := h3 1
  have l10 := h1 1 0 (by decide)
  have l20 := h1 2 0 (by decide)
  have l21 := h1 2 1 (by decide)
  fin_cases i <;> fin_cases a <;> fin_cases c <;> simp [zM] at h d0 d1 d2 s0 s1 ⊢ <;> simp [d0, d1, d2, s0, s1, l10, l20, l21] <;> abel

private theorem natCast_ne (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (hl : (l : O) ≠ 0) (n : ℕ) : n ≠ 0 → (n : O) ≠ 0 := by
  intro hn
  obtain ⟨p, hp⟩ := CharP.exists O
  rcases CharP.char_is_prime_or_zero O p with hpp | rfl
  · exfalso
    have h1 : ((p : ℕ) : ResidueField O) = 0 := by
      rw [← map_natCast (residue O), CharP.cast_eq_zero O p, map_zero]
    haveI : CharP (ResidueField O) l := IsCoef.char
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h1
    have hlp : l = p := (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) hpp).mp h1
    subst hlp
    exact hl (CharP.cast_eq_zero O l)
  · haveI : CharZero O := CharP.charP_to_charZero O
    exact_mod_cast hn

end UpperTheory.V.Z.J.YEx

open UpperTheory.V.Z.J.YEx in
theorem UpperTheory.V.Z.J.yEx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ i : Fin 2, UnitStep I ε t i → ∃ c : O, c ≠ 0 ∧ ∀ k, 0 < k → ∃ y ∈ ZF (l := l) I k t, ∃ s, y s i.castSucc i.castSucc - y s i.succ i.succ = Ideal.Quotient.mk _ c := by
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hGen hT i hU
  have hinv := (cjFacts l O D t 0 hl hT).2.1
  obtain ⟨hdiag, u, β, hu, hβ, hadd, hI, ⟨s0, hs0⟩, hβc⟩ := hU
  obtain ⟨s1, hs1⟩ := hT.dist
  have hχne : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
      - algebraMap ℤ_[l] O (ε s1) ≠ 0 := by
    have h22 := (hinv s1).2 2
    have hε : algebraMap ℤ_[l] O (ε s1) ≠ 0 := ((ε s1).isUnit.map (algebraMap ℤ_[l] O)).ne_zero
    have hi22 : (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 ≠ 0 := by
      intro h
      rw [h, mul_zero] at h22
      exact zero_ne_one h22
    fin_cases i
    · have hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
          = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 := hdiag s1
      have key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
          - algebraMap ℤ_[l] O (ε s1) = algebraMap ℤ_[l] O (ε s1) * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
            * ((t s1 : Matrix (Fin 3) (Fin 3) O) 1 1 - (t s1 : Matrix (Fin 3) (Fin 3) O) 2 2) := by
        linear_combination (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd
          + algebraMap ℤ_[l] O (ε s1) * h22
      rw [key]
      exact mul_ne_zero (mul_ne_zero hε hi22) (hs1 1 2 (by decide)).ne_zero
    · have hd : (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1
          = algebraMap ℤ_[l] O (ε s1) * (t s1 : Matrix (Fin 3) (Fin 3) O) 2 2 := hdiag s1
      have key : (t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
          - algebraMap ℤ_[l] O (ε s1) = (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2
            * ((t s1 : Matrix (Fin 3) (Fin 3) O) 0 0 - (t s1 : Matrix (Fin 3) (Fin 3) O) 1 1) := by
        linear_combination (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 * hd
          + algebraMap ℤ_[l] O (ε s1) * h22
      rw [key]
      exact mul_ne_zero hi22 (hs1 0 1 (by decide)).ne_zero
  refine ⟨((Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
      * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)})).factorial : O) * u s0,
    mul_ne_zero (natCast_ne l O hl _ (Nat.factorial_ne_zero _)) hs0, ?_⟩
  generalize hC : Nat.card (O ⧸ Ideal.span {(t s1 : Matrix (Fin 3) (Fin 3) O) 0 0
      * (((t s1)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2 - algebraMap ℤ_[l] O (ε s1)}) = C
  intro k hk
  obtain ⟨⟨ρ, hρ, hρopen⟩, -, hcj, hsingle, -⟩ := cjFacts l O D t k hl hT
  obtain ⟨hfin, -, hlk, -, hpow, -, -⟩ := okFin l O hl
  haveI := hfin k
  obtain ⟨Nk, hNk⟩ := hpow k
  have hmk : ∀ f : D → O, AdicCont (maximalIdeal O) f →
      IsLocallyConstant (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s)) := by
    intro f hf
    have e : (fun s => Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (f s))
        = (Ideal.Quotient.factor hNk) ∘ (fun g => Ideal.Quotient.mk (maximalIdeal O ^ Nk) (f g)) := by
      funext s
      simp [Ideal.Quotient.factor_mk]
    rw [e]
    exact (hf Nk).comp _
  have hN : ∀ s, matrixEntryZeroTwoSubmodule (Ok l O k) ≤ Submodule.comap (ρ s) (matrixEntryZeroTwoSubmodule (Ok l O k)) := by
    intro s X hX
    rw [Submodule.mem_comap, hρ, eq_single hX, hsingle]
    exact single_mem _
  have hbound : (HomMu l k ε (ρ.subrepresentation (matrixEntryZeroTwoSubmodule (Ok l O k)) hN)).ncard ≤ C := by
    rw [← hC]
    refine homBd l O D ε k _ _ (e02 (Ok l O k))
      (fun s => (t s : Matrix (Fin 3) (Fin 3) O) 0 0 * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) 2 2)
      s1 hl ?_ hχne
    intro s x
    apply Subtype.ext
    show ρ s (Matrix.single 0 2 x) = Matrix.single 0 2 _
    rw [hρ, hsingle]
  have hzlc : IsLocallyConstant (fun s => zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s))) :=
    IsLocallyConstant.comp₂ (hmk u hu) (hmk β hβ) _
  have hzcoc : ∀ s s', zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u (s * s')))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β (s * s')))
      - zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s))
      - ρ s (zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s'))
          (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s'))) ∈ matrixEntryZeroTwoSubmodule (Ok l O k) := by
    intro s s'
    rw [hρ, hadd, map_add]
    have hz' := hcj s _ (zM_upT i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s'))
      (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s')))
    refine zM_coc i _ _ _ _ _ _
      (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.castSucc
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ j.succ)
      (fun j => (t s : Matrix (Fin 3) (Fin 3) O) j.castSucc j.succ
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) j.succ j.succ)
      hz'.1 hz'.2.1 hz'.2.2 ?_
    have hp : (t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.castSucc
        * (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i.succ i.succ = algebraMap ℤ_[l] O (ε s) := by
      rw [hdiag s, mul_assoc, (hinv s).2, mul_one]
    beta_reduce
    rw [hp, hβc, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    simp only [map_add, map_sub, map_mul]
  obtain ⟨y, ⟨hylc, hycoc⟩, hy⟩ := lift l D ε d k hk hLE (Matrix (Fin 3) (Fin 3) (Ok l O k)) ρ
    (fun X => by ext a b; simp [hlk]) hρopen (matrixEntryZeroTwoSubmodule (Ok l O k)) hN C hbound _ hzlc hzcoc
  have hyent : ∀ s (a b : Fin 3), ¬ (a = 0 ∧ b = 2) → y s a b = C.factorial •
      zM i (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (u s)) (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) (β s)) a b := by
    intro s a b hab
    have h := (hy s : ∀ a b : Fin 3, ¬ (a = 0 ∧ b = 2) → _) a b hab
    simp only [Matrix.sub_apply, Matrix.smul_apply] at h
    exact sub_eq_zero.mp h
  have hnd : ∀ j : Fin 3, ¬ (j = 0 ∧ j = 2) := by decide
  refine ⟨y, ?_, s0, ?_⟩
  · show IsLocallyConstant y ∧ (∀ s s', y (s * s') = y s + cj k t s (y s')) ∧ (∀ s, UpT (y s)) ∧
      ∀ s ∈ I, ∀ j : Fin 3, y s j j = 0
    refine ⟨hylc, fun s s' => by rw [hycoc, hρ], ?_, ?_⟩
    · intro s a b hab
      rw [hyent s a b ?_, zM_upT i _ _ a b hab, smul_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (by decide)
    · intro s hs j
      rw [hyent s j j (hnd j), hI s hs, map_zero, zM_diag, smul_zero]
  · rw [hyent s0 _ _ (hnd _), hyent s0 _ _ (hnd _), ← smul_sub, zM_diff, nsmul_eq_mul, map_mul, map_natCast]
