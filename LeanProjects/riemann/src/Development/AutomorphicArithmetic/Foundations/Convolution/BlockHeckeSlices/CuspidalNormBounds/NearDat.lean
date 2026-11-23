import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearBlo
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ResTyp

open NumberField UpperTheory.ConvolutionTheory.BW

noncomputable section

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)}

private abbrev Pt (E : Type) [Field E] [NumberField E] (n : ℕ) : Type :=
  ((E →+* ℂ) × Fin n → ℂ) × (Pl E → Multiset ℂ)

open Classical in
private def inv {n : ℕ} (d : Dat S n) : ℕ × Set (Pt E n) :=
  (d.len, Set.range fun z => (d.ptL z, fun w => if w ∈ S then 0 else d.ptS z w))

private def glue (r s : ℕ) (p : ((E →+* ℂ) → Fin r → ℂ) × (Pl E → Multiset ℂˣ)) (x : ℕ × Set (Pt E s)) :
    ℕ × Set (Pt E (r + s)) :=
  (x.1 + 1, {y | ∃ z : ℂ, ∃ q ∈ x.2, y = (fun a => Fin.addCases (fun i => p.1 a.1 i + z) (fun i => q.1 (a.1, i)) a.2,
    fun w => ((p.2 w).map fun b : ℂˣ => (b : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z)) + q.2 w)})

open Classical in
private theorem pt_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z₀ : ℂ) (z : Fin d.len → ℂ) :
    (((Dat.cons b d).ptL (Fin.cons z₀ z : Fin (d.len + 1) → ℂ),
      fun w => if w ∈ S then 0 else (Dat.cons b d).ptS (Fin.cons z₀ z : Fin (d.len + 1) → ℂ) w) : Pt E (r + s)) =
    (fun a => Fin.addCases (fun i => b.Λ a.1 i + z₀) (fun i => d.ptL z (a.1, i)) a.2,
      fun w => ((if w ∈ S then 0 else b.sat w).map fun b : ℂˣ => (b : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z₀)) +
        if w ∈ S then 0 else d.ptS z w) := by
  refine Prod.ext (funext fun ⟨τ, i⟩ => ?_) (funext fun w => ?_)
  · induction i using Fin.addCases with
    | left i =>
      have e : (Dat.cons b d).idx (Fin.castAdd s i) = (0 : Fin (d.len + 1)) :=
        Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      simp only [Dat.ptL, Dat.lam, Fin.addCases_left]
      rw [e]
      rfl
    | right i =>
      have e : (Dat.cons b d).idx (Fin.natAdd r i) = ((d.idx i).succ : Fin (d.len + 1)) :=
        Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      simp only [Dat.ptL, Dat.lam, Fin.addCases_right]
      rw [e]
      rfl
  · dsimp only
    split_ifs
    · simp
    · exact Fin.sum_univ_succ (n := d.len) _

open Classical in
private theorem inv_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) :
    inv (Dat.cons b d) = glue r s (b.Λ, fun w => if w ∈ S then 0 else b.sat w) (inv d) := by
  refine Prod.ext rfl (Set.ext fun y => ⟨?_, ?_⟩)
  · rintro ⟨z, rfl⟩
    refine ⟨z (0 : Fin (d.len + 1)), _, ⟨Fin.tail (n := d.len) (α := fun _ => ℂ) z, rfl⟩, ?_⟩
    have := pt_cons b d (z (0 : Fin (d.len + 1))) (Fin.tail (n := d.len) (α := fun _ => ℂ) z)
    rw [Fin.cons_self_tail (n := d.len) (α := fun _ => ℂ) z] at this
    exact this
  · rintro ⟨z₀, _, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, pt_cons b d z₀ z⟩

private theorem dat_cases {n : ℕ} (d : Dat S n) :
    (∃ h : 0 = n, d = h ▸ Dat.nil) ∨ ∃ (r s : ℕ) (h : r + s = n) (b : Blo S r) (d' : Dat S s), d = h ▸ Dat.cons b d' := by
  cases d with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b d' => exact Or.inr ⟨_, _, rfl, b, d', rfl⟩

private theorem finite_inv (S : Set (Pl E)) (B : ℝ) (n : ℕ) : ∀ ρ : Typ E n,
    (inv '' {d : Dat S n | d.HasTyp ρ.ρ ∧ ∀ τ i, ‖d.lam τ i‖ ≤ B}).Finite := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ρ
  have h0 : {x | ∃ h : 0 = n, x = inv (h ▸ Dat.nil : Dat S n)}.Finite :=
    Set.Subsingleton.finite (by rintro _ ⟨h, rfl⟩ _ ⟨h', rfl⟩; rfl)
  have h1 : ∀ p ∈ Set.Iic n ×ˢ Set.Iic n, {x | ∃ (h : p.1 + p.2 = n) (b : Blo S p.1) (d' : Dat S p.2),
      (h ▸ Dat.cons b d' : Dat S n).HasTyp ρ.ρ ∧ (∀ τ i, ‖(h ▸ Dat.cons b d' : Dat S n).lam τ i‖ ≤ B) ∧
        x = inv (h ▸ Dat.cons b d' : Dat S n)}.Finite := by
    rintro ⟨r, s⟩ -
    by_cases hp : r + s = n
    swap
    · exact Set.finite_empty.subset (by rintro _ ⟨h, -⟩; exact hp h)
    subst hp
    by_cases hr : 0 < r
    swap
    · exact Set.finite_empty.subset (by rintro _ ⟨-, b, -⟩; exact hr b.pos)
    obtain ⟨⟨ρ₁, c₁, e₁⟩, ⟨ρ₂, c₂, e₂⟩, -⟩ := resTyp E r s ρ
    refine (Set.Finite.image2 (glue r s) (nearBlo E S r ⟨ρ.d, ρ₁, c₁⟩ B) (ih s (by omega) ⟨ρ.d, ρ₂, c₂⟩)).subset ?_
    rintro _ ⟨h, b, d', ⟨k₁, k₂⟩, hB, rfl⟩
    refine ⟨_, ⟨b, ?_, fun τ i => ?_, rfl, fun _ => rfl⟩, _, ⟨d', ⟨?_, fun τ i => ?_⟩, rfl⟩, (inv_cons b d').symm⟩
    · change Killed ρ₁ _
      rw [e₁]; exact k₁
    · simpa only [Dat.lam, Fin.addCases_left] using hB τ (Fin.castAdd s i)
    · change d'.HasTyp ρ₂
      rw [e₂]; exact k₂
    · simpa only [Dat.lam, Fin.addCases_right] using hB τ (Fin.natAdd r i)
  refine (h0.union (((Set.finite_Iic n).prod (Set.finite_Iic n)).biUnion h1)).subset ?_
  rintro _ ⟨d, ⟨hd, hB⟩, rfl⟩
  rcases dat_cases d with ⟨h, rfl⟩ | ⟨r, s, h, b, d', rfl⟩
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr (Set.mem_biUnion (x := (r, s)) ⟨show r ≤ n by omega, show s ≤ n by omega⟩ ⟨h, b, d', hd, hB, rfl⟩)

end

theorem UpperTheory.ConvolutionTheory.BW.nearDat :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.NearDat E := by
  intro E _ _ _ S n ρ B
  obtain ⟨D, -, hD⟩ := Set.exists_subset_bijOn {d : Dat S n | d.HasTyp ρ.ρ ∧ ∀ τ i, ‖d.lam τ i‖ ≤ B} inv
  refine ⟨D, Set.Finite.of_finite_image (by rw [hD.image_eq]; exact finite_inv S B n ρ) hD.injOn, fun d hd hB => ?_⟩
  obtain ⟨d', hd', he⟩ := hD.surjOn ⟨d, ⟨hd, hB⟩, rfl⟩
  refine ⟨d', hd', congrArg Prod.fst he, fun F hF hK z => ?_⟩
  obtain ⟨z', hz⟩ : _ ∈ (inv d').2 := by rw [he]; exact ⟨z, rfl⟩
  rw [← hK z']
  have e₁ : d'.ptL z' = d.ptL z := congrArg Prod.fst hz
  rw [e₁]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun x hx _ => ?_) rfl
  have e₂ := congrFun (congrArg Prod.snd hz) x.1
  simp only [if_neg (hF x hx)] at e₂
  rw [Dat.ptH, Dat.ptH, e₂]
