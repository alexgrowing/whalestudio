import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCW

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab Formalism.BasicNotions.Examples₂

variable {D : D7}

theorem xs_fits (R : Ranks) (t j : ℕ) (hj : j < R.m) : R.k + j * (t + 1) ≤ R.r + j * t - (R.m - j) / 2 := by
  have h1 : j * (t + 1) = j * t + j := by ring
  rw [h1]
  generalize j * t = s
  unfold Ranks.r
  omega

theorem nu_le (R : Ranks) (t j : ℕ) : (R.m - j) / 2 ≤ R.r + j * t := by
  have hk := R.m_add_three_le_k
  have : (R.m - j) / 2 ≤ R.r := by unfold Ranks.r; omega
  omega

def sigTow (D : D7) (t : ℕ) : Tow D t where
  Xs := fun j => posSpace star_isIntegral (D.R.k + j * (t + 1))
  Xs_rank := fun _ _ => rfl
  Xs_sig := fun _ _ => ⟨posSpace_sigOK _ _, fun _ => Or.inl rfl⟩
  Ys := fun j => dSpace star_isIntegral (D.R.r + j * t) ((D.R.m - j) / 2)
  Ys_rank := fun _ _ => rfl
  Ys_sig := fun j _ => dSpace_sigOK _ _ _ (nu_le D.R t j)
  iXYs := fun _ => extLE _ _
  iXYs_isom := fun j hj x y => extLE_isom _ _ ((xs_fits D.R t j hj).trans (Nat.sub_le _ _)) _ _
    (fun i => negTail_false _ _ _ (lt_of_lt_of_le i.isLt (xs_fits D.R t j hj))) x y
  iYXm := extLE _ _
  iYXm_isom := fun x y => extLE_isom _ _ (by
      have := D.R.two_le_m
      unfold Ranks.r
      rw [Nat.mul_succ]
      omega) _ _ (fun i => (negTail_false _ _ _ (by have := i.isLt; omega)).symm) x y

open Classical in

def towC (D : D7) (t : ℕ) : Tow D t := if h : t = D.R.t then h ▸ recTow D else sigTow D t

theorem towC_rec (D : D7) : towC D D.R.t = recTow D := by
  unfold towC
  rw [dif_pos rfl]

def SpSig (D : D7) : Prop :=
  ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef ∧
    ∀ τ, (D.sp.Y j).sig τ = (D.R.r + j * D.R.t - (D.R.m - j) / 2, (D.R.m - j) / 2)

theorem towC_sig (h : SpSig D) (t j : ℕ) (hj : j ≤ D.R.m) : ((towC D t).Xs j).IsPosDef ∧
    ∀ τ, ((towC D t).Ys j).sig τ = (D.R.r + j * t - (D.R.m - j) / 2, (D.R.m - j) / 2) := by
  by_cases e : t = D.R.t
  · subst e
    rw [towC_rec]
    exact h j hj
  · unfold towC
    rw [dif_neg e]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem towC_ok (t j : ℕ) : ((towC D t).Ys j).SigOK := by
  by_cases e : t = D.R.t
  · subst e
    rw [towC_rec]
    exact D.sp.Y_sig j
  · unfold towC
    rw [dif_neg e]
    exact dSpace_sigOK star_isIntegral _ _ (nu_le D.R t j)

def WittLow (D : D7) : Prop := ∀ (V : HSp D) (i : ℕ), (∃ C : Matrix (Fin V.rank) (Fin i) D.host.E, IsIsoSub V C) →
  ∃ V' : HSp D, IsWittLower V V' i

open Classical in

def lowC (V : HSp D) (i : ℕ) : HSp D :=
  if i = 0 then V else if h : ∃ V' : HSp D, IsWittLower V V' i then fixSig h.choose else V

theorem lowC_spec (hW : WittLow D) (V : HSp D) (hV : V.SigOK) (i : ℕ)
    (h : ∃ C : Matrix (Fin V.rank) (Fin i) D.host.E, IsIsoSub V C) : IsWittLower V (lowC V i) i ∧ (lowC V i).SigOK := by
  unfold lowC
  by_cases e : i = 0
  · subst e
    rw [if_pos rfl]
    obtain ⟨C, hC⟩ := h
    exact ⟨⟨rfl, LinearMap.id, fun _ _ => rfl, C, hC, Subsingleton.elim _ _⟩, hV⟩
  · have h' := hW V i h
    rw [if_neg e, dif_pos h']
    exact ⟨h'.choose_spec, fixSig_ok _⟩

def EmbU (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ g g' h, EmbRel A B ι g h → EmbRel A B ι g' h → g = g'

def EmbRat (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ γ ∈ GQ B, ∃ γ' ∈ GQ A, EmbRel A B ι γ' γ

theorem embRel_mul {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} {g g' : GA D A} {h h' : GA D B} (a : EmbRel A B ι g h)
    (b : EmbRel A B ι g' h') : EmbRel A B ι (g * g') (h * h') := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, b.1, ← Matrix.mul_assoc, a.1, Matrix.mul_assoc]
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, b.2 x hx, a.2 x hx]

def EmbCond (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Prop :=
  HSpace.IsIsomEmb B A ι ∧ ∃ s : GA D B → GA D A, ∀ h, EmbRel A B ι (s h) h

def embC {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι) : GA D B → GA D A := h.2.choose

theorem embC_spec {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι) (x : GA D B) : EmbRel A B ι (embC h x) x :=
  h.2.choose_spec x

theorem embC_left (hU : EmbU D) (hR : EmbRat D) {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι)
    {γ : GA D B} (hγ : γ ∈ GQ B) : ∃ γ' ∈ GQ A, EmbRel A B ι γ' γ ∧ ∀ x, embC h (γ * x) = γ' * embC h x := by
  obtain ⟨γ', a, b⟩ := hR A B ι h.1 γ hγ
  exact ⟨γ', a, b, fun x => hU A B ι h.1 _ _ _ (embC_spec h _) (embRel_mul b (embC_spec h x))⟩

def TopInt (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ s : GA D B → GA D A, (∀ h, EmbRel A B ι (s h) h) →
  ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ (s h)) * F h) 𝓕 μ

open Classical in

def btopC (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (φ : afC D A) (F : cuspC D B) : ℂ :=
  if h : EmbCond A B ι then (petCOf D petF (petRC D) B : ℂ) * intC B fun x => star (φ.1 (embC h x)) * F.1.1 x else 0

theorem top_int (G : FormGaps D) (hI : TopInt D) {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι) (φ : afC D A)
    (F : cuspC D B) : IntegrableOn (fun x => star (φ.1 (embC h x)) * F.1.1 x) (pairC B).2 (pairC B).1 :=
  hI A B ι h.1 _ (embC_spec h) _ _ (pairC_spec G.volEx B).1 (pairC_spec G.volEx B).2.1 _ _ ((mem_afC G.add).1 φ.2)
    ((mem_afC G.add).1 F.1.2) ((mem_cuspC G.add G.cuspInt).1 F.2)

theorem btopC_right (G : FormGaps D) (hI : TopInt D) (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V)
    (φ : afC D A) : IsLinearMap ℂ (btopC petF A B ι φ) := by
  unfold btopC intC
  by_cases h : EmbCond A B ι
  · simp only [dif_pos h]
    refine ⟨fun F F' => ?_, fun c F => ?_⟩
    · rw [← mul_add, ← integral_add (top_int G hI h φ F) (top_int G hI h φ F')]
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    · rw [smul_eq_mul, mul_left_comm, ← integral_const_mul c]
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm c]
  · simp only [dif_neg h]
    exact ⟨fun _ _ => by simp, fun _ _ => by simp⟩

theorem btopC_add (G : FormGaps D) (hI : TopInt D) (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V)
    (φ φ' : afC D A) (F : cuspC D B) : btopC petF A B ι (φ + φ') F = btopC petF A B ι φ F + btopC petF A B ι φ' F := by
  unfold btopC intC
  by_cases h : EmbCond A B ι
  · simp only [dif_pos h]
    rw [← mul_add, ← integral_add (top_int G hI h φ F) (top_int G hI h φ' F)]
    simp only [Submodule.coe_add, Pi.add_apply, star_add, add_mul]
  · simp only [dif_neg h, add_zero]

theorem pairing_smul_left₂ (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V)
    (c : ℂ) (φ : afC D A) (F : cuspC D B) : btopC petF A B ι (c • φ) F = star c * btopC petF A B ι φ F := by
  unfold btopC intC
  by_cases h : EmbCond A B ι
  · simp only [dif_pos h]
    rw [mul_left_comm, ← integral_const_mul (star c)]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
  · simp only [dif_neg h, mul_zero]

theorem btopC_eq (G : FormGaps D) (hU : EmbU D) (hR : EmbRat D) (petF : HSp D → ℝ) (A B : HSp D)
    (ι : B.V →ₗ[D.host.E] A.V) (hB : B.SigOK) (hι : HSpace.IsIsomEmb B A ι) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (hp : IsVolPair D B μ 𝓕) (s : GA D B → GA D A) (hs : ∀ h, EmbRel A B ι (s h) h) (φ : afC D A) (F : cuspC D B) :
    btopC petF A B ι φ F = (petCOf D petF (petRC D) B : ℂ) * ∫ h in 𝓕, star (φ.1 (s h)) * F.1.1 h ∂μ := by
  have h : EmbCond A B ι := ⟨hι, s, hs⟩
  have e : s = embC h := funext fun x => hU A B ι hι _ _ _ (hs x) (embC_spec h x)
  unfold btopC
  rw [dif_pos h, e, intC_eq G.volEx G.volU hB hp]
  intro γ hγ x
  obtain ⟨γ', a, -, b⟩ := embC_left hU hR h hγ
  rw [b, ((mem_afC G.add).1 φ.2).left γ' a, ((mem_afC G.add).1 F.1.2).left γ hγ]

section Bessel

variable (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def NPair (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B d.e) p.2 p.1 ∧ p.1 p.2 = 1

def besIn (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) (F : GA D B → ℂ) (x : GA D B) : ℂ :=
  ∫ n in p.2, F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B)) ∂p.1

end Bessel

def BesInt1 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p, NPair d p → ∀ F : GA D B → ℂ, IsAutFun B F → ∀ x,
    IntegrableOn (fun n : NFlag B d.e => F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B))) p.2 p.1

def BesInv (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p p', NPair d p → NPair d p' → ∀ F : GA D B → ℂ, IsAutFun B F →
    ∀ γ' ∈ GQ B, ∀ γ : GA D A, EmbRel B A ι γ' γ → ∀ x, besIn ψ d p F (γ' * x) = besIn ψ d p' F x

def BesInt2 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  HSpace.IsIsomEmb A B ι → ∀ p, NPair d p → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
  ∀ (μ : Measure (GA D A)) (𝓕 : Set (GA D A)), μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsCuspFun A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ h) * besIn ψ d p F (s h * (d.y : GA D B))) 𝓕 μ

theorem proj_ex (A : HSp D) : ∃ g : afC D A →ₗ[ℂ] cuspC D A, g ∘ₗ (cuspC D A).subtype = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)

def projC (A : HSp D) : afC D A →ₗ[ℂ] cuspC D A := (proj_ex A).choose

theorem projC_eq (A : HSp D) (φ : afC D A) (h : φ ∈ cuspC D A) : (projC A φ).1 = φ := by
  have := LinearMap.congr_fun (proj_ex A).choose_spec ⟨φ, h⟩
  exact congrArg Subtype.val this

structure PerGaps (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  embU : EmbU D
  embRat : EmbRat D
  topInt : TopInt D
  int1 : BesInt1 ψ
  inv : BesInv ψ
  int2 : BesInt2 ψ

section Bessel2

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

open Classical in

def besC (ψ : AddChar (AF D.host.F) ℂ) (petF : HSp D → ℝ) (d : BesDat A B ι) (φ : afC D A) (F : cuspC D B) : ℂ :=
  if h : EmbCond B A ι ∧ ∃ p, NPair d p then
    (petCOf D petF (petRC D) A : ℂ) *
      intC A fun x => star ((projC A φ).1.1 x) * besIn ψ d h.2.choose F.1.1 (embC h.1 x * (d.y : GA D B))
  else 0

theorem bes_int (G : FormGaps D) (P : PerGaps ψ) (d : BesDat A B ι) (h : EmbCond B A ι ∧ ∃ p, NPair d p) (φ : afC D A)
    (F : cuspC D B) : IntegrableOn
      (fun x => star ((projC A φ).1.1 x) * besIn ψ d h.2.choose F.1.1 (embC h.1 x * (d.y : GA D B))) (pairC A).2 (pairC A).1 :=
  P.int2 A B ι d h.1.1 _ h.2.choose_spec _ (embC_spec h.1) _ _ (pairC_spec G.volEx A).1 (pairC_spec G.volEx A).2.1 _ _
    ((mem_afC G.add).1 (projC A φ).1.2) ((mem_cuspC G.add G.cuspInt).1 (projC A φ).2)
    ((mem_afC G.add).1 F.1.2) ((mem_cuspC G.add G.cuspInt).1 F.2)

theorem besC_right (G : FormGaps D) (P : PerGaps ψ) (petF : HSp D → ℝ) (d : BesDat A B ι) (φ : afC D A) :
    IsLinearMap ℂ (besC ψ petF d φ) := by
  unfold besC intC
  by_cases h : EmbCond B A ι ∧ ∃ p, NPair d p
  · simp only [dif_pos h]
    refine ⟨fun F F' => ?_, fun c F => ?_⟩
    · rw [← mul_add, ← integral_add (bes_int G P d h φ F) (bes_int G P d h φ F')]
      congr 2
      funext x
      rw [← mul_add]
      congr 1
      unfold besIn
      rw [← integral_add (P.int1 A B ι d _ h.2.choose_spec _ ((mem_afC G.add).1 F.1.2).toIsAutFun _)
        (P.int1 A B ι d _ h.2.choose_spec _ ((mem_afC G.add).1 F'.1.2).toIsAutFun _)]
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    · rw [smul_eq_mul, mul_left_comm, ← integral_const_mul c]
      congr 2
      funext x
      unfold besIn
      rw [mul_left_comm c, ← integral_const_mul c]
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · simp only [dif_neg h]
    exact ⟨fun _ _ => by simp, fun _ _ => by simp⟩

theorem besC_add (G : FormGaps D) (P : PerGaps ψ) (petF : HSp D → ℝ) (d : BesDat A B ι) (φ φ' : afC D A) (F : cuspC D B) :
    besC ψ petF d (φ + φ') F = besC ψ petF d φ F + besC ψ petF d φ' F := by
  unfold besC intC
  by_cases h : EmbCond B A ι ∧ ∃ p, NPair d p
  · simp only [dif_pos h]
    rw [← mul_add, ← integral_add (bes_int G P d h φ F) (bes_int G P d h φ' F)]
    simp only [map_add, Submodule.coe_add, Pi.add_apply, star_add, add_mul]
  · simp only [dif_neg h, add_zero]

theorem besC_smul (petF : HSp D → ℝ) (d : BesDat A B ι) (c : ℂ) (φ : afC D A) (F : cuspC D B) :
    besC ψ petF d (c • φ) F = star c * besC ψ petF d φ F := by
  unfold besC intC
  by_cases h : EmbCond B A ι ∧ ∃ p, NPair d p
  · simp only [dif_pos h]
    rw [mul_left_comm, ← integral_const_mul (star c)]
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
  · simp only [dif_neg h, mul_zero]

theorem embRel_one (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : EmbRel A B ι 1 1 := by
  refine ⟨?_, fun x _ => ?_⟩
  · rw [map_one, map_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem besC_eq (G : FormGaps D) (P : PerGaps ψ) (petF : HSp D → ℝ) (d : BesDat A B ι) (hA : A.SigOK)
    (hι : HSpace.IsIsomEmb A B ι) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (hp : IsVolPair D A μ 𝓕)
    (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) (hN : NPair d p) (s : GA D A → GA D B)
    (hs : ∀ h, EmbRel B A ι (s h) h) (φ : afC D A) (F : cuspC D B) (hφ : IsAniso A ∨ φ ∈ cuspC D A) :
    besC ψ petF d φ F = (petCOf D petF (petRC D) A : ℂ) *
      ∫ h in 𝓕, ∫ n in p.2, star (φ.1 h) * F.1.1 ((n : GA D B) * s h * (d.y : GA D B)) *
        star (besChar ψ d (n : GA D B)) ∂p.1 ∂μ := by
  have h : EmbCond B A ι ∧ ∃ p, NPair d p := ⟨⟨hι, s, hs⟩, p, hN⟩
  have e : s = embC h.1 := funext fun x => P.embU B A ι hι _ _ _ (hs x) (embC_spec h.1 x)
  have hc : φ ∈ cuspC D A := hφ.elim (fun a => Submodule.subset_span fun r C hC => absurd hC (a r C)) id
  have hF := ((mem_afC G.add).1 F.1.2).toIsAutFun
  unfold besC
  rw [dif_pos h, projC_eq A φ hc, intC_eq G.volEx G.volU hA hp]
  · congr 2
    funext x
    have e1 := P.inv A B ι d _ p h.2.choose_spec hN _ hF 1 (one_mem _) 1 (embRel_one B A ι) (embC h.1 x * (d.y : GA D B))
    rw [one_mul] at e1
    rw [e1, e]
    unfold besIn
    rw [← integral_const_mul]
    simp only [mul_assoc]
  · intro γ hγ x
    obtain ⟨γ', a, a', b⟩ := embC_left P.embU P.embRat h.1 hγ
    rw [b, ((mem_afC G.add).1 φ.2).left γ hγ, mul_assoc γ',
      P.inv A B ι d _ _ h.2.choose_spec h.2.choose_spec _ hF γ' a γ a']

end Bessel2

end Formalism.L2.Fam.ThC

end
