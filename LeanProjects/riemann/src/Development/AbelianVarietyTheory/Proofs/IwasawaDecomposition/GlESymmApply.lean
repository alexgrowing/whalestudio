import Mathlib
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt

noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix Classical
open scoped TensorProduct

section Local

@[ext] structure Pr (R V k : Type) [CommRing R] [AddCommGroup V] [Module R V] where
  L : Submodule R V
  f : V → k

variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

structure Pr.Ok (res : R →+* k) (p : Pr R V k) : Prop where
  sat : ∀ s x, res s ≠ 0 → s • x ∈ p.L → x ∈ p.L
  add : ∀ x ∈ p.L, ∀ y ∈ p.L, p.f (x + y) = p.f x + p.f y
  smul : ∀ a, ∀ x ∈ p.L, p.f (a • x) = res a * p.f x
  off : ∀ x, x ∉ p.L → p.f x = 0
  ne : ∃ x, p.f x ≠ 0

def Pr.IsKer (q : Pr R V k) (Λ : Submodule R V) : Prop := ∀ y, y ∈ Λ ↔ y ∈ q.L ∧ q.f y = 0

def Pr.Inc (res : R →+* k) (t : R) (p q : Pr R V k) : Prop :=
  q.Ok res ∧ q.IsKer p.L ∧ ∃ e, q.f e = 1 ∧ p.f (t • e) = 1

def Pr.act (g : V ≃ₗ[R] V) (p : Pr R V k) : Pr R V k := ⟨p.L.map (g : V →ₗ[R] V), fun x => p.f (g.symm x)⟩

def Pr.dil (a : k) (p : Pr R V k) : Pr R V k := ⟨p.L, fun x => a * p.f x⟩

structure Red (res : R →+* k) (t : R) (Λ : Submodule R V) {W : Type} [AddCommGroup W] [Module k W] (π : V → W) : Prop where
  add : ∀ x ∈ Λ, ∀ y ∈ Λ, π (x + y) = π x + π y
  smul : ∀ a, ∀ x ∈ Λ, π (a • x) = res a • π x
  surj : ∀ w, ∃ x ∈ Λ, π x = w
  ker : ∀ x ∈ Λ, π x = 0 ↔ ∃ y ∈ Λ, ∃ s, res s ≠ 0 ∧ s • x = t • y

example : Pr.Ok (RingHom.id k) (⟨⊤, id⟩ : Pr k k k) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => (h trivial).elim, ⟨1, one_ne_zero⟩⟩

example : Red (RingHom.id k) 0 (⊤ : Submodule k k) (id : k → k) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun w => ⟨w, trivial, rfl⟩, fun x _ =>
    ⟨fun h => ⟨0, trivial, 1, one_ne_zero, by simpa using h⟩, fun ⟨_, _, s, hs, h⟩ => by
      have h' : s * x = 0 := by simpa using h
      exact (mul_eq_zero.1 h').resolve_left hs⟩⟩

def Unram (res : R →+* k) (t : R) : Prop := res t = 0 ∧ ∀ a, res a = 0 → ∃ s b, res s ≠ 0 ∧ s * a = t * b

abbrev loc (res : R →+* k) (M : Submodule R V) : Submodule R V :=
  @Formalism.HermitianLatticesTheory.localization₂ R _ V _ _ (RingHom.ker res) (RingHom.ker_isPrime res) M

theorem mem_loc (res : R →+* k) (M : Submodule R V) (x : V) : x ∈ loc res M ↔ ∃ s, res s ≠ 0 ∧ s • x ∈ M :=
  @rlv_mem_locP R V _ _ _ (RingHom.ker res) (RingHom.ker_isPrime res) M x

theorem le_loc (res : R →+* k) (M : Submodule R V) : M ≤ loc res M := fun x hx =>
  (mem_loc res M x).2 ⟨1, by simp, by simpa using hx⟩

theorem loc_sat (res : R →+* k) (M : Submodule R V) (s : R) (x : V) (hs : res s ≠ 0) (h : s • x ∈ loc res M) :
    x ∈ loc res M := by
  obtain ⟨s', hs', h'⟩ := (mem_loc res M _).1 h
  exact (mem_loc res M x).2 ⟨s' * s, by rw [map_mul]; exact mul_ne_zero hs' hs, by rwa [mul_smul]⟩

variable {W : Type} [AddCommGroup W] [Module k W]

def locExt (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (x : V) : W :=
  if h : ∃ s, res s ≠ 0 ∧ s • x ∈ M then (res h.choose)⁻¹ • pr ⟨_, h.choose_spec.2⟩ else 0

theorem locExt_off (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (x : V) (hx : x ∉ loc res M) :
    locExt res M pr x = 0 := dif_neg (fun h => hx ((mem_loc res M x).2 h))

theorem locExt_spec (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (hs : ∀ (a : R) z, pr (a • z) = res a • pr z)
    (x : V) (hx : x ∈ loc res M) (a : R) (h : a • x ∈ M) : pr ⟨a • x, h⟩ = res a • locExt res M pr x := by
  have h0 := (mem_loc res M x).1 hx
  unfold locExt
  rw [dif_pos h0]
  have h1 := h0.choose_spec
  have e : h0.choose • (⟨a • x, h⟩ : M) = a • ⟨_, h1.2⟩ := Subtype.ext (smul_comm _ _ _)
  have := congrArg pr e
  rw [hs, hs] at this
  rw [smul_comm, ← this, smul_smul, inv_mul_cancel₀ h1.1, one_smul]

theorem locExt_coe (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (hs : ∀ (a : R) z, pr (a • z) = res a • pr z)
    (z : M) : locExt res M pr z = pr z := by
  have := locExt_spec res M pr hs z (le_loc res M z.2) 1 (by simp)
  rw [map_one, one_smul k] at this
  rw [← this]; congr 1; exact Subtype.ext (one_smul _ _)

theorem locExt_add (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (hs : ∀ (a : R) z, pr (a • z) = res a • pr z)
    (x : V) (hx : x ∈ loc res M) (y : V) (hy : y ∈ loc res M) :
    locExt res M pr (x + y) = locExt res M pr x + locExt res M pr y := by
  obtain ⟨s, hs0, h1⟩ := (mem_loc res M x).1 hx
  obtain ⟨s', hs0', h2⟩ := (mem_loc res M y).1 hy
  have h1' : (s' * s) • x ∈ M := by rw [mul_smul]; exact M.smul_mem _ h1
  have h2' : (s' * s) • y ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem _ h2
  have h3 : (s' * s) • (x + y) ∈ M := by rw [smul_add]; exact M.add_mem h1' h2'
  have hne : res (s' * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hs0' hs0
  apply smul_right_injective W hne
  simp only [smul_add]
  rw [← locExt_spec res M pr hs _ hx _ h1', ← locExt_spec res M pr hs _ hy _ h2',
    ← locExt_spec res M pr hs _ (add_mem hx hy) _ h3, ← map_add]
  congr 1; exact Subtype.ext (smul_add _ _ _)

theorem locExt_smul (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (hs : ∀ (a : R) z, pr (a • z) = res a • pr z)
    (a : R) (x : V) (hx : x ∈ loc res M) : locExt res M pr (a • x) = res a • locExt res M pr x := by
  obtain ⟨s, hs0, h1⟩ := (mem_loc res M x).1 hx
  have h2 : s • a • x ∈ M := by rw [smul_comm]; exact M.smul_mem _ h1
  apply smul_right_injective W hs0
  simp only
  rw [← locExt_spec res M pr hs _ (Submodule.smul_mem _ a hx) _ h2, smul_comm (res s) (res a),
    ← locExt_spec res M pr hs _ hx _ h1, ← hs]
  congr 1; exact Subtype.ext (smul_comm _ _ _)

theorem locExt_red (res : R →+* k) (t : R) (hu : Unram res t) (M : Submodule R V) (pr : M →+ W)
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hsurj : Function.Surjective pr)
    (hker : ∀ z, pr z = 0 ↔ z.1 ∈ RingHom.ker res • M) : Red res t (loc res M) (locExt res M pr) := by
  refine ⟨locExt_add res M pr hs, locExt_smul res M pr hs, fun w => ?_, fun x hx => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨z, rfl⟩ := hsurj w
    exact ⟨z, le_loc res M z.2, locExt_coe res M pr hs z⟩
  · obtain ⟨s, hs0, h1⟩ := (mem_loc res M x).1 hx
    have h2 := locExt_spec res M pr hs x hx s h1
    rw [h, smul_zero, hker] at h2
    have key : ∀ z ∈ RingHom.ker res • M, ∃ y ∈ M, ∃ s, res s ≠ 0 ∧ s • z = t • y := by
      intro z hz
      refine Submodule.smul_induction_on hz (fun a ha m hm => ?_) ?_
      · obtain ⟨s, b, h3, h4⟩ := hu.2 a ha
        exact ⟨b • m, M.smul_mem _ hm, s, h3, by rw [smul_smul, smul_smul, h4]⟩
      · rintro a b ⟨y, hy, s, h3, h4⟩ ⟨y', hy', s', h3', h4'⟩
        refine ⟨s' • y + s • y', M.add_mem (M.smul_mem _ hy) (M.smul_mem _ hy'), s' * s,
          by rw [map_mul]; exact mul_ne_zero h3' h3, ?_⟩
        rw [smul_add, smul_add, mul_smul, h4, mul_comm, mul_smul, h4', smul_comm t s', smul_comm t s]
    obtain ⟨y, hy, s', h3, h4⟩ := key _ h2
    exact ⟨y, le_loc res M hy, s' * s, by rw [map_mul]; exact mul_ne_zero h3 hs0, by rw [mul_smul]; exact h4⟩
  · rintro ⟨y, hy, s, hs0, h⟩
    have h1 := locExt_smul res M pr hs s x hx
    rw [h, locExt_smul res M pr hs t y hy, hu.1, zero_smul] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left hs0

def pairOf (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (φ : Module.Dual k W) : Pr R V k :=
  ⟨loc res M, fun x => φ (locExt res M pr x)⟩

theorem pairOf_ok (res : R →+* k) (M : Submodule R V) (pr : M →+ W) (φ : Module.Dual k W)
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hsurj : Function.Surjective pr) (hφ : φ ≠ 0) :
    (pairOf res M pr φ).Ok res := by
  refine ⟨loc_sat res M, fun x hx y hy => ?_, fun a x hx => ?_, fun x hx => ?_, ?_⟩
  · show φ _ = φ _ + φ _
    rw [locExt_add res M pr hs x hx y hy, map_add]
  · show φ _ = _ * φ _
    rw [locExt_smul res M pr hs a x hx, map_smul, smul_eq_mul]
  · show φ _ = 0
    rw [locExt_off res M pr x hx, map_zero]
  · by_contra h
    push Not at h
    apply hφ
    ext w
    obtain ⟨z, rfl⟩ := hsurj w
    have := h z
    change φ _ = 0 at this
    rwa [locExt_coe res M pr hs] at this

theorem Pr.mem_act (g : V ≃ₗ[R] V) (p : Pr R V k) (x : V) : x ∈ (p.act g).L ↔ g.symm x ∈ p.L :=
  Submodule.mem_map_equiv _

theorem Pr.act_act (g g' : V ≃ₗ[R] V) (p : Pr R V k) : (p.act g).act g' = p.act (g.trans g') := by
  ext x
  · simp only [Pr.mem_act]; rfl
  · rfl

theorem Pr.act_refl (p : Pr R V k) : p.act (LinearEquiv.refl R V) = p := by
  ext x
  · simp only [Pr.mem_act]; rfl
  · rfl

theorem Pr.act_injective (g : V ≃ₗ[R] V) : Function.Injective (Pr.act g : Pr R V k → Pr R V k) := by
  intro p q h
  have := congrArg (Pr.act g.symm) h
  rwa [Pr.act_act, Pr.act_act, LinearEquiv.self_trans_symm, Pr.act_refl, Pr.act_refl] at this

theorem Pr.act_dil (g : V ≃ₗ[R] V) (a : k) (p : Pr R V k) : (p.dil a).act g = (p.act g).dil a := rfl

theorem Pr.dil_dil (a b : k) (p : Pr R V k) : (p.dil a).dil b = p.dil (b * a) := by
  ext x
  · rfl
  · exact (mul_assoc _ _ _).symm

theorem Pr.dil_one (p : Pr R V k) : p.dil 1 = p := by
  ext x
  · rfl
  · exact one_mul _

theorem Pr.Ok.act {res : R →+* k} {p : Pr R V k} (h : p.Ok res) (g : V ≃ₗ[R] V) : (p.act g).Ok res := by
  refine ⟨fun s x hs hx => ?_, fun x hx y hy => ?_, fun a x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [Pr.mem_act] at hx ⊢
    rw [map_smul] at hx; exact h.sat s _ hs hx
  · rw [Pr.mem_act] at hx hy
    show p.f _ = p.f _ + p.f _
    rw [map_add, h.add _ hx _ hy]
  · rw [Pr.mem_act] at hx
    show p.f _ = _ * p.f _
    rw [map_smul, h.smul _ _ hx]
  · rw [Pr.mem_act] at hx
    exact h.off _ hx
  · obtain ⟨x, hx⟩ := h.ne
    exact ⟨g x, by show p.f _ ≠ 0; rwa [g.symm_apply_apply]⟩

theorem Pr.Ok.dil {res : R →+* k} {p : Pr R V k} (h : p.Ok res) {a : k} (ha : a ≠ 0) : (p.dil a).Ok res := by
  refine ⟨h.sat, fun x hx y hy => ?_, fun b x hx => ?_, fun x hx => ?_, ?_⟩
  · show a * _ = a * _ + a * _
    rw [h.add _ hx _ hy, mul_add]
  · show a * _ = _ * (a * _)
    rw [h.smul _ _ hx]; ring
  · show a * _ = 0
    rw [h.off _ hx, mul_zero]
  · obtain ⟨x, hx⟩ := h.ne
    exact ⟨x, mul_ne_zero ha hx⟩

theorem Pr.Inc.act {res : R →+* k} {t : R} {p q : Pr R V k} (h : Pr.Inc res t p q) (g : V ≃ₗ[R] V) :
    Pr.Inc res t (p.act g) (q.act g) := by
  obtain ⟨h1, h2, e, h3, h4⟩ := h
  refine ⟨h1.act g, fun y => ?_, g e, ?_, ?_⟩
  · rw [Pr.mem_act, Pr.mem_act]; exact h2 _
  · show q.f _ = 1
    rwa [g.symm_apply_apply]
  · show p.f _ = 1
    rwa [← map_smul, g.symm_apply_apply]

theorem Pr.inc_act_iff {res : R →+* k} {t : R} (p q : Pr R V k) (g : V ≃ₗ[R] V) :
    Pr.Inc res t (p.act g) (q.act g) ↔ Pr.Inc res t p q := by
  refine ⟨fun h => ?_, fun h => h.act g⟩
  have := h.act g.symm
  rwa [Pr.act_act, Pr.act_act, LinearEquiv.self_trans_symm, Pr.act_refl, Pr.act_refl] at this

end Local

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

def glE (γ : GL (Fin n) E) : (Fin n → E) ≃ₗ[𝓞 E] (Fin n → E) :=
  LinearEquiv.ofLinear ((Matrix.mulVecLin γ.1).restrictScalars (𝓞 E)) ((Matrix.mulVecLin (γ⁻¹).1).restrictScalars (𝓞 E))
    (LinearMap.ext fun x => by
      show γ.1 *ᵥ ((γ⁻¹).1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])
    (LinearMap.ext fun x => by
      show (γ⁻¹).1 *ᵥ (γ.1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec])

theorem glE_apply (γ : GL (Fin n) E) (x : Fin n → E) : glE γ x = γ.1 *ᵥ x := rfl
theorem glE_symm_apply (γ : GL (Fin n) E) (x : Fin n → E) : (glE γ).symm x = (γ⁻¹).1 *ᵥ x := rfl
theorem map_glE (γ : GL (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    L.map (glE γ : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)) = mulLat γ.1 L := rfl
theorem glE_mul (γ γ' : GL (Fin n) E) : glE (γ * γ') = (glE γ').trans (glE γ) := by
  ext1 x; simp [glE_apply, Matrix.mulVec_mulVec]
theorem glE_one : glE (1 : GL (Fin n) E) = LinearEquiv.refl _ _ := by
  ext1 x; simp [glE_apply]

abbrev GA (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : Type := UPts σ J (FiniteAdeleRing (𝓞 F) F)

def AtV (v : HeightOneSpectrum (𝓞 F)) (η : GA σ J) : Prop := ∀ v', v' ≠ v → bc (prV (E := E) v') η.1 = 1

def MulsF (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∃ hg : h ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
    ∀ x : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      a • S.fT v hv ⟨h.1 *ᵥ x.1, (hg x.1).1 x.2⟩ = S.fT v hv x

def PMap (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : Type} [Field k]
    (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) : Prop :=
  (∀ γ ∈ UJ (σ : E →+* E) J, ∀ x x' : GA σ J, x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 →
    p x' = (p x).act (glE γ)) ∧
  (∀ x δ : GA σ J, p (x * δ) = p x ↔ bc (prV (E := E) v) δ.1 ∈ S.Uloc v) ∧
  ∀ (x δ : GA σ J) (a : ℤ), IsDia S v hv a δ → p (x * δ) = (p x).dil (a : k)

def valAt {k M : Type} [Zero M] (v : HeightOneSpectrum (𝓞 F)) (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) (g : GA σ J → M) (x : GA σ J)
    (q : Pr (𝓞 E) (Fin n → E) k) : M :=
  if h : ∃ η, AtV v η ∧ p (x * η) = q then g (x * h.choose) else 0

def upAd {k M : Type} [Field k] [AddCommMonoid M] (res : 𝓞 E →+* k) (t : 𝓞 E) (v : HeightOneSpectrum (𝓞 F))
    (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) (g : GA σ J → M) (x : GA σ J) : M :=
  ∑ᶠ q ∈ {q | Pr.Inc res t (p x) q}, valAt v p g x q

end Adelic

section Tied

variable {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}

def pc (P : LvTied u A i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v) :=
  pairOf (A.res v) (Ld D u i hi c) (P.pr v c) ((D.fm u).fv i v c)

theorem pc_ok (P : LvTied u A i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : (pc P v c).Ok (A.res v) :=
  pairOf_ok _ _ _ _ (P.pr_smul v c) (P.pr_surj v c) ((D.fm u).fv_ne i v c)

abbrev mov (K : ClsTied u i hi) (v : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (γ : GL (Fin (D.R.N i)) D.host.E) (c' : (D.mem u).C.cls i) :
    GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
  bc (prV (E := D.host.E) v) ((K.y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (K.y c').1)

abbrev dualV (K : ClsTied u i hi) (v : HeightOneSpectrum (𝓞 D.host.F)) :=
  latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cls_le_dual (K : ClsTied u i hi) (c : (D.mem u).C.cls i) : clsCrd D u i hi c ≤ Ld D u i hi c := by
  intro x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
    intro z hz
    exact (K.y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ K.lev.Lb, ∀ b ∈ K.lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := K.lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) K.lev.Lb 1 hm (K.y c).1
    (K.y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact bwL_descent _ _ _ h

theorem pc_isKer (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    (pc P v c).IsKer (loc (A.res v) (Lk A i hi v c)) := by
  have hle : Lk A i hi v c ≤ Ld D u i hi c := sup_le (cls_le_dual K c) Submodule.smul_le_right
  intro y
  constructor
  · intro hy
    obtain ⟨s, hs, h⟩ := (mem_loc _ _ _).1 hy
    have hy' : y ∈ loc (A.res v) (Ld D u i hi c) := (mem_loc _ _ _).2 ⟨s, hs, hle h⟩
    refine ⟨hy', ?_⟩
    have h1 := (P.fv_ker v c ⟨_, hle h⟩).2 h
    rw [locExt_spec _ _ _ (P.pr_smul v c) y hy' s (hle h), map_smul, smul_eq_zero] at h1
    exact h1.resolve_left hs
  · rintro ⟨hy, h0⟩
    obtain ⟨s, hs, h⟩ := (mem_loc _ _ _).1 hy
    refine (mem_loc _ _ _).2 ⟨s, hs, (P.fv_ker v c ⟨_, h⟩).1 ?_⟩
    rw [locExt_spec _ _ _ (P.pr_smul v c) y hy s h, map_smul]
    change (D.fm u).fv i v c _ = 0 at h0
    rw [h0, smul_zero]

end Tied

end GlobalTheory.LevelHecke

end
