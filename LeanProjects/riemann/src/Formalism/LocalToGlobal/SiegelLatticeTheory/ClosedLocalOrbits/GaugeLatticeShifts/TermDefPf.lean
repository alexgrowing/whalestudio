import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem frame_castSucc_td {T : E} (F : LFlag S r T) (i : Fin r) : frame F i.castSucc = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last_td {T : E} (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem mem_gmap_iff {Λ : Submodule (𝓞 E) S.V} (g : S.V ≃ₗ[E] S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap g Λ ↔ g.symm x ∈ Λ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g.symm x, h, by simp⟩

theorem gmap_eq_iff {Λ : Submodule (𝓞 E) S.V} (g : S.V ≃ₗ[E] S.V) :
    Formalism.HermitianLatticesTheory.gmap g Λ = Λ ↔ ∀ x, g x ∈ Λ ↔ x ∈ Λ := by
  constructor
  · intro h x
    have := (mem_gmap_iff (Λ := Λ) g (g x))
    rw [h] at this
    simpa using this
  · intro h
    ext x
    rw [mem_gmap_iff]
    have := h (g.symm x)
    simpa using this.symm

theorem isAutLam_iff (Λ : Submodule (𝓞 E) S.V) (g : S.V ≃ₗ[E] S.V) :
    IsAutLam S Λ g ↔ (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ ∀ x, g x ∈ Λ ↔ x ∈ Λ := by
  unfold IsAutLam
  rw [gmap_eq_iff]
  rfl

theorem isAutLam_mul {Λ : Submodule (𝓞 E) S.V} {g h : S.V ≃ₗ[E] S.V} (hg : IsAutLam S Λ g)
    (hh : IsAutLam S Λ h) : IsAutLam S Λ (g * h) := by
  rw [isAutLam_iff] at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp only [LinearEquiv.mul_apply]
    rw [hg.1, hh.1]
  · simp only [LinearEquiv.mul_apply]
    rw [hg.2, hh.2]

theorem isAutLam_inv {Λ : Submodule (𝓞 E) S.V} {g : S.V ≃ₗ[E] S.V} (hg : IsAutLam S Λ g) :
    IsAutLam S Λ g⁻¹ := by
  rw [isAutLam_iff] at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have := hg.1 (g⁻¹ x) (g⁻¹ y)
    simpa using this.symm
  · have := hg.2 (g⁻¹ x)
    simpa using this.symm

theorem xflag_mono_td {T : E} (F : LFlag S r T) {j k : ℕ} (h : j ≤ k) : Xflag F j ≤ Xflag F k := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  exact lt_of_lt_of_le hi h

theorem xflag_zero_td {T : E} (F : LFlag S r T) : Xflag F 0 = ⊥ := by
  simp [Xflag, FlagG.Xa]

theorem xflag_r {T : E} (F : LFlag S r T) : Xflag F r = Xsp F := by
  simp only [Xflag, FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext x
  simp

theorem nlam_mapsTo {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, n x ∈ Xflag F j := by
  intro x hx
  cases j with
  | zero =>
    rw [xflag_zero_td] at hx ⊢
    rw [Submodule.mem_bot] at hx ⊢
    simp [hx]
  | succ k =>
    have h1 := hn.2.1 k x hx
    have h2 : n x = x + (n x - x) := by abel
    rw [h2]
    exact Submodule.add_mem _ hx (xflag_mono_td F (Nat.le_succ k) h1)

theorem nlam_map_eq {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (j : ℕ) : (Xflag F j).map (n : S.V →ₗ[E] S.V) = Xflag F j := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    exact nlam_mapsTo hn j x hx
  · exact LinearEquiv.finrank_map_eq n _

theorem mem_orth_iff_td {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ y ∈ U, S.hT y v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem nlam_orth_mapsTo {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : ∀ x ∈ orth S (Xsp F), n x ∈ orth S (Xsp F) := by
  intro x hx
  rw [mem_orth_iff_td] at hx ⊢
  intro y hy
  have hy' : y ∈ (Xsp F).map (n : S.V →ₗ[E] S.V) := by
    rw [← xflag_r, nlam_map_eq hn r]
    rwa [xflag_r]
  obtain ⟨y', hy'X, rfl⟩ := hy'
  have hiso := ((isAutLam_iff Λ n).1 hn.1).1
  simp only [LinearEquiv.coe_coe]
  rw [hiso]
  exact hx y' hy'X

theorem nlam_orth_map_eq {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : (orth S (Xsp F)).map (n : S.V →ₗ[E] S.V) = orth S (Xsp F) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    exact nlam_orth_mapsTo hn x hx
  · exact LinearEquiv.finrank_map_eq n _

theorem nlamPf_mul {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n p : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) (hp : p ∈ NLam Λ F) : n * p ∈ NLam Λ F := by
  refine ⟨isAutLam_mul hn.1 hp.1, ?_, ?_⟩
  · intro j x hx
    have e : (n * p) x - x = (n (p x) - p x) + (p x - x) := by
      simp only [LinearEquiv.mul_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hn.2.1 j _ (nlam_mapsTo hp (j + 1) x hx)) (hp.2.1 j x hx)
  · intro x hx
    have e : (n * p) x - x = (n (p x) - p x) + (p x - x) := by
      simp only [LinearEquiv.mul_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hn.2.2 _ (nlam_orth_mapsTo hp x hx)) (hp.2.2 x hx)

theorem nlamPf_inv {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) : n⁻¹ ∈ NLam Λ F := by
  refine ⟨isAutLam_inv hn.1, ?_, ?_⟩
  · intro j x hx
    rw [← nlam_map_eq hn (j + 1)] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have e : n⁻¹ ((n : S.V →ₗ[E] S.V) y) - (n : S.V →ₗ[E] S.V) y = -(n y - y) := by
      simp
    rw [e]
    exact Submodule.neg_mem _ (hn.2.1 j y hy)
  · intro x hx
    rw [← nlam_orth_map_eq hn] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have e : n⁻¹ ((n : S.V →ₗ[E] S.V) y) - (n : S.V →ₗ[E] S.V) y = -(n y - y) := by
      simp
    rw [e]
    exact Submodule.neg_mem _ (hn.2.2 y hy)

theorem mem_xflag_of_frame {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ : S.V ≃ₗ[E] S.V}
    (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (j : ℕ) (x : S.V) :
    x ∈ Xflag F₂ j ↔ γ.symm x ∈ Xflag F₁ j := by
  have he : ∀ i, F₂.fl.e i = γ (F₁.fl.e i) := by
    intro i
    have := hF i.castSucc
    rwa [frame_castSucc_td, frame_castSucc_td] at this
  have hm : Xflag F₂ j = (Xflag F₁ j).map (γ : S.V →ₗ[E] S.V) := by
    simp only [Xflag, FlagG.Xa, Submodule.map_span]
    congr 1
    ext y
    simp [he]
  rw [hm]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

theorem mem_xsp_of_frame {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ : S.V ≃ₗ[E] S.V}
    (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (x : S.V) :
    x ∈ Xsp F₂ ↔ γ.symm x ∈ Xsp F₁ := by
  rw [← xflag_r, ← xflag_r]
  exact mem_xflag_of_frame hF r x

theorem mem_orth_of_frame {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ : S.V ≃ₗ[E] S.V}
    (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) (x : S.V) :
    x ∈ orth S (Xsp F₂) ↔ γ.symm x ∈ orth S (Xsp F₁) := by
  rw [mem_orth_iff_td, mem_orth_iff_td]
  constructor
  · intro h y hy
    have := h (γ y) (by rw [mem_xsp_of_frame hF]; simpa using hy)
    rw [← hγ y (γ.symm x)]
    simpa using this
  · intro h y hy
    have := h (γ.symm y) ((mem_xsp_of_frame hF y).1 hy)
    rw [← hγ (γ.symm y) (γ.symm x)] at this
    simpa using this

theorem nlam_conj {Λ : Submodule (𝓞 E) S.V} {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂} {γ p : S.V ≃ₗ[E] S.V}
    (hγ : IsAutLam S Λ γ) (hF : ∀ a, frame F₂ a = γ (frame F₁ a)) (hp : p ∈ NLam Λ F₁) :
    γ * p * γ⁻¹ ∈ NLam Λ F₂ := by
  have hiso := ((isAutLam_iff Λ γ).1 hγ).1
  refine ⟨isAutLam_mul (isAutLam_mul hγ hp.1) (isAutLam_inv hγ), ?_, ?_⟩
  · intro j x hx
    rw [mem_xflag_of_frame hF] at hx ⊢
    have := hp.2.1 j _ hx
    have e : γ.symm ((γ * p * γ⁻¹) x - x) = p (γ.symm x) - γ.symm x := by
      simp only [LinearEquiv.mul_apply, map_sub]
      simp [LinearEquiv.coe_inv]
    rw [e]
    exact this
  · intro x hx
    rw [mem_orth_of_frame hF hiso] at hx
    rw [mem_xsp_of_frame hF]
    have := hp.2.2 _ hx
    have e : γ.symm ((γ * p * γ⁻¹) x - x) = p (γ.symm x) - γ.symm x := by
      simp only [LinearEquiv.mul_apply, map_sub]
      simp [LinearEquiv.coe_inv]
    rw [e]
    exact this

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T)

theorem dcrel_symm {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : DCRel Λ F F₂ F₁ := by
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := h
  have hγ : IsAutLam S Λ (n * m) := isAutLam_mul hn.1 hm.1
  have hF : ∀ a, frame F₂ a = (n * m) (frame F₁ a) := fun a => by simpa using hfr a
  have hm' := nlam_conj hγ hF (nlamPf_inv hm)
  refine ⟨n⁻¹, nlamPf_inv hn, n * m * m⁻¹ * (n * m)⁻¹, hm', fun a => ?_, ?_⟩
  · have key : n⁻¹ * (n * m * m⁻¹ * (n * m)⁻¹) * (n * m) = 1 := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q (frame F₁ a)) key
    simp only [LinearEquiv.mul_apply] at this
    rw [hfr a]
    simpa using this.symm
  · have key : n⁻¹ * (n * m * m⁻¹ * (n * m)⁻¹) * (n * m) = 1 := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q F₁.zt) key
    simp only [LinearEquiv.mul_apply] at this
    rw [hzt]
    simpa using this.symm

theorem dcrel_trans {F₁ F₂ F₃ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) (h' : DCRel Λ F F₂ F₃) :
    DCRel Λ F F₁ F₃ := by
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := h
  obtain ⟨n', hn', m', hm', hfr', hzt'⟩ := h'
  have hγ : IsAutLam S Λ (n * m)⁻¹ := isAutLam_inv (isAutLam_mul hn.1 hm.1)
  have hF : ∀ a, frame F₁ a = (n * m)⁻¹ (frame F₂ a) := fun a => by
    rw [hfr a]; simp [LinearEquiv.coe_inv]
  have hm'' := nlam_conj hγ hF hm'
  refine ⟨n' * n, nlamPf_mul hn' hn, m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹), nlamPf_mul hm hm'', fun a => ?_, ?_⟩
  · have key : (n' * n) * (m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹)) = n' * m' * (n * m) := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q (frame F₁ a)) key
    rw [hfr' a, hfr a]
    simp only [LinearEquiv.mul_apply] at this ⊢
    exact this.symm
  · have key : (n' * n) * (m * ((n * m)⁻¹ * m' * (n * m)⁻¹⁻¹)) = n' * m' * (n * m) := by group
    have := congrArg (fun q : S.V ≃ₗ[E] S.V => q F₁.zt) key
    rw [hzt', hzt]
    simp only [LinearEquiv.mul_apply] at this ⊢
    exact this.symm

variable (P : LFlag S r T' → Prop)

theorem double_coset_equivalence : EqIff Λ F P := by
  intro x y
  constructor
  · intro h
    have hq := Quot.eqvGen_exact h
    clear h
    induction hq with
    | rel a b hab => exact hab
    | refl a => exact dcrel_refl Λ F a.1
    | symm a b _ ih => exact dcrel_symm Λ F ih
    | trans a b c _ _ ih1 ih2 => exact dcrel_trans Λ F ih1 ih2
  · intro h
    exact Quot.sound h

section Zhat

variable {Λ : Submodule (𝓞 E) S.V}

theorem frame_sub_mem_span {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F)
    (a : Fin (r + 1)) : n (frame F a) - frame F a ∈ Submodule.span E (frame F '' {c | c < a}) := by
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last_td]
    have hz : F.fl.z ∈ orth S (Xsp F) := by
      rw [mem_orth_iff_td]
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        exact F.fl.z_orth i
      · simp
      · intro x y _ _ hx hy
        simp [map_add, hx, hy]
      · intro c x _ hx
        simp [hx]
    have := hn.2.2 _ hz
    refine Submodule.span_mono ?_ this
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, Fin.castSucc_lt_last i, frame_castSucc_td F i⟩
  | cast i =>
    rw [frame_castSucc_td]
    have hx : F.fl.e i ∈ Xflag F (i.1 + 1) := Submodule.subset_span ⟨i, by simp, rfl⟩
    have := hn.2.1 i.1 _ hx
    refine Submodule.span_mono ?_ this
    rintro _ ⟨i', hi', rfl⟩
    exact ⟨i'.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hi', frame_castSucc_td F i'⟩

theorem nlam_coef {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    ∃ α : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a c, a < c → α a c = 0) ∧ (∀ a, α a a = 1) ∧
      ∀ a, n (frame F a) = ∑ c, α a c • frame F c := by
  have h := fun a => (Finsupp.mem_span_image_iff_linearCombination E).1 (frame_sub_mem_span hn a)
  choose l hl hsum using h
  have hz : ∀ a c, ¬ c < a → l a c = 0 := fun a c hc => (Finsupp.mem_supported' _ _).1 (hl a) c hc
  refine ⟨fun a c => (if a = c then 1 else 0) + l a c, ?_, ?_, ?_⟩
  · intro a c hac
    simp [ne_of_lt hac, hz a c (not_lt.2 (le_of_lt hac))]
  · intro a
    simp [hz a a (lt_irrefl a)]
  · intro a
    have e := hsum a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [e]
    abel

theorem zhat_rel {T T' : E} (F : LFlag S r T) {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) :
    ∃ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a c, a < c → A a c = 0) ∧ (∀ a, A a a = 1) ∧
      (∀ d b, b < d → B d b = 0) ∧ (∀ b, B b b = 1) ∧ ZhatL F F₂ = A * ZhatL F F₁ * B := by
  obtain ⟨n, hn, m, hm, hfr, -⟩ := h
  obtain ⟨α, hα0, hα1, hα⟩ := nlam_coef (nlamPf_inv hn)
  obtain ⟨β, hβ0, hβ1, hβ⟩ := nlam_coef hm
  refine ⟨α.map star, β.transpose, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c h
    simp [hα0 a c h]
  · intro a
    simp [hα1]
  · intro d b h
    simp [Matrix.transpose_apply, hβ0 b d h]
  · intro b
    simp [hβ1]
  · ext a b
    have hiso := ((isAutLam_iff Λ n).1 hn.1).1
    have e1 : ZhatL F F₂ a b = S.hT (n⁻¹ (frame F a)) (m (frame F₁ b)) := by
      change S.hT (frame F a) (frame F₂ b) = _
      rw [hfr b, ← hiso (n⁻¹ (frame F a)) (m (frame F₁ b))]
      simp
    rw [e1, hα a, hβ b]
    simp only [Matrix.mul_apply, ZhatL, Zhat, brS, map_sum, map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring

theorem sum_castLE_td {N l : ℕ} (h : l ≤ N) (g : Fin N → E) (hg : ∀ d : Fin N, l ≤ d.1 → g d = 0) :
    ∑ d, g d = ∑ d' : Fin l, g (Fin.castLE h d') := by
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ g ?_ (fun _ => rfl)).symm
  intro d hd
  apply hg
  by_contra hlt
  exact hd ⟨⟨d.1, by omega⟩, Fin.ext (by simp)⟩

theorem leadMinor_uni {N : ℕ} (A Z B : Matrix (Fin N) (Fin N) E) (hA0 : ∀ a c, a < c → A a c = 0)
    (hA1 : ∀ a, A a a = 1) (hB0 : ∀ d b, b < d → B d b = 0) (hB1 : ∀ b, B b b = 1) (l : ℕ) :
    leadMinorE (A * Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · have hsub : (A * Z * B).submatrix (Fin.castLE h) (Fin.castLE h) =
        A.submatrix (Fin.castLE h) (Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
          B.submatrix (Fin.castLE h) (Fin.castLE h) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [sum_castLE_td h]
      · refine Finset.sum_congr rfl (fun d _ => ?_)
        congr 1
        rw [sum_castLE_td h]
        intro c hc
        rw [hA0 _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]
      · intro d hd
        rw [hB0 _ _ (by rw [Fin.lt_def]; simp; omega), mul_zero]
    rw [hsub, Matrix.det_mul, Matrix.det_mul]
    have hA : (A.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · simp [hA1]
      · intro i j hij
        exact hA0 _ _ (by
          have : i < j := hij
          rw [Fin.lt_def] at this ⊢
          simpa using this)
    have hB : (B.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · simp [hB1]
      · intro i j hij
        exact hB0 _ _ (by
          have : j < i := hij
          rw [Fin.lt_def] at this ⊢
          simpa using this)
    rw [hA, hB, one_mul, mul_one]
  · rfl

theorem gval_rel {T T' : E} (F : LFlag S r T) {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) :
    Gval F F₂ = Gval F F₁ := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := zhat_rel F h
  have hD : ∀ l, Dl F.fl F₂.fl l = Dl F.fl F₁.fl l := by
    intro l
    have := leadMinor_uni A (ZhatL F F₁) B hA0 hA1 hB0 hB1 l
    rw [← hZ] at this
    exact this
  simp only [Gval, Gflag, hD]

theorem isLoUni_mul {N : ℕ} {A L : Matrix (Fin N) (Fin N) E} (hA : IsLoUni A) (hL : IsLoUni L) :
    IsLoUni (A * L) := by
  intro i j
  constructor
  · intro hij
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge i k with h | h
    · simp [(hA i k).1 h]
    · simp [(hL k j).1 (lt_of_le_of_lt h hij)]
  · rintro rfl
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · simp [(hA i i).2 rfl, (hL i i).2 rfl]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [(hL k i).1 h]
      · simp [(hA i k).1 h]
    · simp

theorem isUpUni_mul {N : ℕ} {U V : Matrix (Fin N) (Fin N) E} (hU : IsUpUni U) (hV : IsUpUni V) :
    IsUpUni (U * V) := by
  intro i j
  constructor
  · intro hij
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge k i with h | h
    · simp [(hU i k).1 h]
    · simp [(hV k j).1 (lt_of_lt_of_le hij h)]
  · rintro rfl
    simp only [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · simp [(hU i i).2 rfl, (hV i i).2 rfl]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [(hU i k).1 h]
      · simp [(hV k i).1 h]
    · simp

theorem zhatOM_mul (A Z B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ZhatOM (A * Z * B) =
      A * ZhatOM Z * Matrix.of (fun d b => (-1 : E) ^ (r - d.val) * B d b * (-1) ^ (r - b.val)) := by
  have hs : ∀ k : ℕ, (-1 : E) ^ k * (-1) ^ k = 1 := fun k => by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  ext a b
  simp only [ZhatOM, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))
  linear_combination (-(A a c * Z c d * B d b * (-1) ^ (r - b.val))) * hs (r - d.val)

theorem cell_rel {T T' : E} (F : LFlag S r T) {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂)
    (w : Point E (r + 1)) (hc : IsInCell (ZhatOM (ZhatL F F₁)) w) :
    IsInCell (ZhatOM (ZhatL F F₂)) w := by
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := zhat_rel F h
  obtain ⟨L, U, hL, hU, hLU⟩ := hc
  refine ⟨A * L, U * Matrix.of (fun d b => (-1 : E) ^ (r - d.val) * B d b * (-1) ^ (r - b.val)),
    isLoUni_mul (fun i j => ⟨hA0 i j, fun e => e ▸ hA1 i⟩) hL, isUpUni_mul hU ?_, ?_⟩
  · intro i j
    constructor
    · intro hij
      simp [Matrix.of_apply, hB0 i j hij]
    · rintro rfl
      rw [Matrix.of_apply, hB1, mul_one, ← pow_add, ← two_mul, pow_mul]
      simp
  · rw [hZ, zhatOM_mul, hLU]
    simp only [Matrix.mul_assoc]

end Zhat

section Props

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop)

theorem g_value_function : GFun Λ F P := fun _ _ h => (gval_rel F h).symm

theorem cell_function_holds : CellFun Λ F P := fun _ _ h w =>
  ⟨cell_rel F h w, cell_rel F (dcrel_symm Λ F h) w⟩

end Props

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem term_equivalence_iff (u u' : D.what₂.Word) : TermEqIff D u u' :=
  fun F0 Λ _ => double_coset_equivalence Λ (lf D F0) _

end D7

end Formalism.L2.SG.Pf
