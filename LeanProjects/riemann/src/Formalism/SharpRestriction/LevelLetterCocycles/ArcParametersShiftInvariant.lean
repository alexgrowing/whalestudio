import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Comb

variable {n : ℕ} (a : ZMod n)

def sh {α : Type*} (f : ZMod n → α) : ZMod n → α := fun i => f (i - a)

def shC (cuts : Finset (ZMod n)) : Finset (ZMod n) := cuts.image (· + a)

theorem mem_shC {cuts : Finset (ZMod n)} {c : ZMod n} : c ∈ shC a cuts ↔ c - a ∈ cuts := by
  simp only [shC, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨c - a, h, sub_add_cancel c a⟩

theorem ellMax_sh (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ellMax (shC a cuts) (sh a arcLen) = ellMax cuts arcLen := by
  unfold ellMax shC
  rw [Finset.sup_image]
  congr 1
  funext x
  simp [sh]

theorem cutsOK_sh {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : CutsOK n j ty cuts arcLen) : CutsOK n j (sh a ty) (shC a cuts) (sh a arcLen) := by
  obtain ⟨hne, hj, h3, h4, h5⟩ := h
  refine ⟨hne.image _, hj, fun c hc ↦ ?_, fun c hc ↦ h4 _ ((mem_shC a).1 hc), fun c hc k hk1 hkj ↦ ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := h3 _ ((mem_shC a).1 hc)
    refine ⟨e1, e2, (mem_shC a).2 ?_, fun d hd1 hd2 hmem ↦ e4 d hd1 hd2 ?_⟩
    · rw [sub_right_comm]
      exact e3
    · have hm := (mem_shC a).1 hmem
      rwa [sub_right_comm] at hm
  · show ty (c + (k : ZMod n) - a) = LT.thin
    rw [show c + (k : ZMod n) - a = c - a + k by ring]
    exact h5 _ ((mem_shC a).1 hc) k hk1 hkj

theorem ro_sh (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) :
    ro (sh a ty) (sh a arcLen) c = ro ty arcLen (c - a) := by
  rw [Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.thickLv, Formalism.MainNotions.LocalTheoryWindows.thickLv]
  congr 1
  apply Finset.filter_congr
  intro s _
  simp only [sh]
  rw [show c - (s : ZMod n) - a = c - a - s by ring]

theorem thickLe2_sh {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : ThickLe2 ty cuts arcLen) : ThickLe2 (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc
  rw [ro_sh]
  exact h _ ((mem_shC a).1 hc)

theorem wordOK_sh {l a₀ : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : WordOK l a₀ ty cuts arcLen) : WordOK l a₀ (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc s₀ s₁ hs hs1 b₀ b₁
  have h' := h _ ((mem_shC a).1 hc) s₀ s₁ hs hs1 b₀ b₁
  simp only [sh]
  rw [sub_right_comm c (s₁ : ZMod n) a, sub_right_comm c (s₀ : ZMod n) a]
  exact h'

theorem sizesOK_sh {g S h : ℕ} {ty : ZMod n → LT} (H : SizesOK g S h ty) :
    SizesOK g S h (sh a ty) := fun i ↦ H (i - a)

variable [NeZero n]

theorem Hmax_sh (H : ZMod n → ℕ) : Hmax n (sh a H) = Hmax n H := by
  unfold Hmax
  apply le_antisymm
  · exact Finset.sup_le fun i _ ↦ Finset.le_sup (f := H) (Finset.mem_univ (i - a))
  · refine Finset.sup_le fun i _ ↦ ?_
    have hle := Finset.le_sup (f := sh a H) (Finset.mem_univ (i + a))
    simpa [sh] using hle

theorem sBd_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : sBd l n (sh a H) i = sBd l n H (i - a) := by
  unfold sBd
  rw [Hmax_sh]
  congr 1
  funext k
  simp only [sh]
  rw [show i + ((k + 1 : ℕ) : ZMod n) - a = i - a + ((k + 1 : ℕ) : ZMod n) by ring]

theorem rF_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : rF l n (sh a H) i = rF l n H (i - a) := by
  unfold rF
  rw [sBd_sh, Hmax_sh]

theorem rrPar_sh (l : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) :
    rrPar l n (sh a H₁) (sh a H₂) (shC a cuts) = rrPar l n H₁ H₂ cuts := by
  unfold rrPar shC
  rw [Finset.sup_image]
  congr 1
  funext c
  simp only [Function.comp_apply, rF_sh, add_sub_cancel_right]

theorem arc_parameters_shift_invariant (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    initialExponentBound l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      initialExponentBound l n j g h H₁ H₂ cuts arcLen := by
  unfold initialExponentBound
  rw [rrPar_sh, ellMax_sh]

theorem ePar_sh (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ePar l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      ePar l n j g h H₁ H₂ cuts arcLen := by
  unfold ePar
  rw [rrPar_sh, arc_parameters_shift_invariant, ellMax_sh]

end Comb

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem jumpsAtE_sh (T : LocLat G Qp LL O) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a i : ZMod n) (S : Set ℤ)
    (h : JumpsAtE PD T (fun k => emb (k + a)) (i - a) S) : JumpsAtE PD T emb i S := by
  intro τ hτ
  exact h τ (by simp only [sub_add_cancel]; exact hτ)

theorem exists_rot {emb emb' : ZMod n → (K₀ →ₐ[Qp] LL)} (hb : Function.Surjective emb')
    (h : ∀ i, (emb (i + 1)).comp PD.σ = emb i) (h' : ∀ i, (emb' (i + 1)).comp PD.σ = emb' i) :
    ∃ a : ZMod n, emb = fun i => emb' (i + a) := by
  obtain ⟨a, ha⟩ := hb (emb 0)
  refine ⟨a, ?_⟩
  have key : ∀ k : ℕ, emb (-(k : ZMod n)) = emb' (-(k : ZMod n) + a) := by
    intro k
    induction k with
    | zero => simp [ha]
    | succ k ih =>
      have e1 := h (-((k + 1 : ℕ) : ZMod n))
      have e2 := h' (-((k + 1 : ℕ) : ZMod n) + a)
      rw [show -((k + 1 : ℕ) : ZMod n) + 1 = -(k : ZMod n) by push_cast; ring, ih] at e1
      rw [show -((k + 1 : ℕ) : ZMod n) + a + 1 = -(k : ZMod n) + a by push_cast; ring] at e2
      rw [← e1, e2]
  funext i
  have hi := key ((-i).val)
  rwa [ZMod.natCast_zmod_val, neg_neg] at hi

variable [Fintype (K →ₐ[Qp] LL)]

theorem thmELiftAt_rot (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a : ZMod n)
    (H : ThmELiftAt PD (O := O) n emb v) : ThmELiftAt PD (O := O) n (fun i => emb (i + a)) v := by
  intro hLet hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hKind hJ hg
    hSizes hCuts hThick hJ1 hJ2 hWord
  have hLet' : Letters PD LL v emb := by
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hLet
    refine ⟨e1, e2, e3, ?_, fun i ↦ ?_, e6⟩
    · have he : emb = (fun i ↦ emb (i + a)) ∘ (fun i ↦ i - a) := funext fun i ↦ by simp
      rw [he]
      exact e4.comp (Equiv.subRight a).bijective
    · have e := e5 (i - a)
      simp only [sub_add_cancel, show i - a + 1 + a = i + 1 by ring] at e
      exact e
  have hW : WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (sh a Mb₁ + sh a hb₁) (sh a Mb₂ + sh a hb₂)
      (shC a cuts) (sh a arcLen)) (sh a ty) (shC a cuts) (sh a arcLen) := by
    rw [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
      show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, arc_parameters_shift_invariant]
    exact wordOK_sh a hWord
  have hL := H hLet' hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h (sh a ty) (shC a cuts) (sh a arcLen)
    (sh a Mb₁) (sh a hb₁) (sh a Mb₂) (sh a hb₂) (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hKind (i - a))) hJ hg
    (sizesOK_sh a hSizes) (cutsOK_sh a hCuts) (thickLe2_sh a hThick)
    (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hJ1 (i - a))) (fun i ↦ jumpsAtE_sh T₂ emb a i _ (hJ2 (i - a))) hW
  rwa [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
    show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, ePar_sh] at hL

end Formalism.MainNotions.WachCoordinates.Br
