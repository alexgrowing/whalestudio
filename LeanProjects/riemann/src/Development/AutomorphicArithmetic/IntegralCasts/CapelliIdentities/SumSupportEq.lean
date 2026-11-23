import Mathlib

open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yfa1.MRing.{u_1, u_2, u_3} :
    {K : Type u_1} → (K → Type u_2) → (R : Type u_3) → [CommRing R] → Type (max u_3 u_2 u_1) :=
    fun {K : Type u_1} (ι : K → Type u_2) (R : Type u_3) [CommRing R] ↦ MvPolynomial ((k : K) × ι k) R

noncomputable def UpperTheory.Reformulated.B.Yfa1.cycEval.{u_1, u_2, u_3} :
    {K : Type u_1} →
      {ι : K → Type u_2} →
        {R : Type u_3} →
          [inst : CommRing R] → (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R) → ℤ) → (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R) → ℤ) → ℤ :=
    fun {K : Type u_1} {ι : K → Type u_2} {R : Type u_3} [CommRing R] (n Z : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R) → ℤ) ↦
      ∑ᶠ (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι R)), Z W * n W

noncomputable def UpperTheory.Reformulated.B.Yfa1.eventualValue.{u_1} :
    {K : Type u_1} → ((K → ℤ) → ℤ) → ℤ :=
    fun {K : Type u_1} (f : (K → ℤ) → ℤ) ↦
      if h : ∃ (c : ℤ), ∀ᶠ (m : K → ℤ) in Filter.atTop, f m = c then h.choose else (0 : ℤ)

noncomputable def UpperTheory.Reformulated.B.Yfa1.diffStep.{u_1} :
    {K : Type u_1} → (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} (b : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) ↦ h m - h (m - b)

noncomputable def UpperTheory.Reformulated.B.Yfa1.mixedDiff.{u_1} :
    {K : Type u_1} → {n : ℕ} → (Fin n → K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) ↦
      List.foldr UpperTheory.Reformulated.B.Yfa1.diffStep h (List.ofFn bs)

noncomputable def UpperTheory.Reformulated.B.Yfa1.blockWeight.{u_1, u_2} :
    {K : Type u_1} → (ι : K → Type u_2) → [DecidableEq K] → (k : K) × ι k → K → ℕ :=
    fun {K : Type u_1} (ι : K → Type u_2) [DecidableEq K] (v : (k : K) × ι k) ↦ Pi.single v.fst (1 : ℕ)

noncomputable def UpperTheory.Reformulated.B.Yfa1.gradedPiece.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {F : Type u_3} →
            [inst : Field F] →
              (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F)) → (K → ℕ) → Submodule F (UpperTheory.Reformulated.B.Yfa1.MRing ι F ⧸ P) :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {F : Type u_3} [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F))
        (m : K → ℕ) ↦
      Submodule.map (Ideal.Quotient.mkₐ F P).toLinearMap
        (MvPolynomial.weightedHomogeneousSubmodule F (UpperTheory.Reformulated.B.Yfa1.blockWeight ι) m)

noncomputable def UpperTheory.Reformulated.B.Yfa1.hilbFn.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} → {F : Type u_3} → [inst : Field F] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {F : Type u_3} [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F))
        (m : K → ℤ) ↦
      if ∀ (k : K), (0 : ℤ) ≤ m k then (↑(Module.finrank F ↥(UpperTheory.Reformulated.B.Yfa1.gradedPiece P fun (k : K) ↦ (m k).toNat)) : ℤ)
      else (0 : ℤ)

noncomputable def UpperTheory.Reformulated.B.Yfa1.intNum.{u_1, u_2, u_4} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          (F : Type u_4) → [inst : Field F] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F) → {n : ℕ} → (Fin n → K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} (F : Type u_4) [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι F))
        {n : ℕ} (bs : Fin n → K → ℤ) ↦
      UpperTheory.Reformulated.B.Yfa1.eventualValue (UpperTheory.Reformulated.B.Yfa1.mixedDiff bs (UpperTheory.Reformulated.B.Yfa1.hilbFn P))

noncomputable def UpperTheory.Reformulated.B.Yfa1.specialIdeal.{u_1, u_2, u_3} :
    {K : Type u_1} →
      {ι : K → Type u_2} →
        {O : Type u_3} →
          [inst : CommRing O] →
            [inst_1 : IsDomain O] →
              [inst_2 : IsDiscreteValuationRing O] →
                Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι (IsLocalRing.ResidueField O)) :=
    fun {K : Type u_1} {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) ↦
      Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) W

noncomputable def UpperTheory.Reformulated.B.Yfa1.vNum.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {O : Type u_3} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] →
                [IsDiscreteValuationRing O] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → {n : ℕ} → (Fin n → K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) {n : ℕ} (bs : Fin n → K → ℤ) ↦
      UpperTheory.Reformulated.B.Yfa1.intNum (IsLocalRing.ResidueField O) (UpperTheory.Reformulated.B.Yfa1.specialIdeal W) bs

noncomputable def UpperTheory.Reformulated.B.Yfa1.vNumL.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {O : Type u_3} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] → [IsDiscreteValuationRing O] → Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → List (K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) (l : List (K → ℤ)) ↦
      UpperTheory.Reformulated.B.Yfa1.vNum W l.get

noncomputable def UpperTheory.Reformulated.B.Yfa1.cycList :
    {K : Type} →
      {ι : K → Type} →
        [DecidableEq K] →
          {O : Type} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] →
                [IsDiscreteValuationRing O] → (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) → List (K → ℤ) → ℤ :=
    fun {K : Type} {ι : K → Type} [DecidableEq K] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        (Z : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) (l : List (K → ℤ)) ↦
      UpperTheory.Reformulated.B.Yfa1.cycEval (fun (W : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O)) ↦ UpperTheory.Reformulated.B.Yfa1.vNumL W l) Z

noncomputable def UpperTheory.Reformulated.B.Yfa1.classList.{u_1, u_3} :
    {K : Type u_1} → {σ : Type u_3} → (σ → K → ℤ) → (σ →₀ ℕ) → List (K → ℤ) :=
    fun {K : Type u_1} {σ : Type u_3} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) ↦
      (Multiset.map cls ((Finsupp.toMultiset : (σ →₀ ℕ) → Multiset σ) μ)).toList

noncomputable def UpperTheory.Reformulated.B.Yfa1.cycNum :
    {K : Type} →
      {ι : K → Type} →
        {σ : Type} →
          [DecidableEq K] →
            {O : Type} →
              [inst : CommRing O] →
                [inst_1 : IsDomain O] →
                  [IsDiscreteValuationRing O] →
                    (Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) → (σ → K → ℤ) → MvPolynomial σ ℝ → List (K → ℤ) → ℝ :=
    fun {K : Type} {ι : K → Type} {σ : Type} [DecidableEq K] {O : Type} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (Z : Ideal (UpperTheory.Reformulated.B.Yfa1.MRing ι O) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
        (Q : List (K → ℤ)) ↦
      ∑ μ ∈ H.support, MvPolynomial.coeff μ H * (↑(UpperTheory.Reformulated.B.Yfa1.cycList Z (UpperTheory.Reformulated.B.Yfa1.classList cls μ ++ Q)) : ℝ)
