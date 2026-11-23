import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt

noncomputable section

namespace Formalism.L2.Pj

section Charts

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

abbrev locM (K : Type) [Field K] {S : Type} [CommRing S] [Algebra K S] (m : Ideal S) [m.IsPrime] :
    S →ₐ[K] Localization.AtPrime m :=
  IsScalarTower.toAlgHom K S (Localization.AtPrime m)

def FrChartAt {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsPrime] (A : TRing K)
    (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m) : Prop :=
  ∀ (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R), mapR φ y w →
    ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R) (a : A.R →ₐ[K] p'.R) (μ : p'.R →ₐ[K] Localization.AtPrime m)
      (y' : pts p'.R), mapR lam y y' ∧ mapR a u y' ∧ μ.comp lam = (locM K m).comp φ ∧ μ.comp a = c

def FrChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsMaximal],
    ∃ (A : TRing K) (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m), FrChartAt pts mapR w m A u c

def BorChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
    ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m) (B : TRing K) (uB uB' : pts B.R)
        (tB : ι → (B.R)ˣ) (π π' : A.R →ₐ[K] B.R) (cB : B.R →ₐ[K] Localization.AtPrime m),
        FrChartAt pts mapR w m A u c ∧ FrChartAt pts mapR w' m A u c' ∧ mapR π u uB ∧ mapR π' u uB' ∧
          borR tB uB uB' ∧ cB.comp π = c ∧ cB.comp π' = c' ∧ ∀ i, cB (tB i : B.R) = locM K m (t i : S)

variable {pts mapR borR}

theorem chartAt_val {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type} [CommRing S] [Algebra K S] {w : pts S}
    {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hc : FrChartAt pts mapR w m A u c) {p : TRing K} {φ : p.R →ₐ[K] S} {y : pts p.R} (hy : mapR φ y w) :
    locM K m (φ (f p y)) = c (f A u) := by
  obtain ⟨p', lam, a, μ, y', h1, h2, h3, h4⟩ := hc p φ y hy
  have e1 : f p' y' = lam (f p y) := hf p p' lam y y' h1
  have e2 : f p' y' = a (f A u) := hf A p' a u y' h2
  calc locM K m (φ (f p y)) = ((locM K m).comp φ) (f p y) := rfl
    _ = (μ.comp lam) (f p y) := by rw [h3]
    _ = μ (f p' y') := by rw [e1]; rfl
    _ = (μ.comp a) (f A u) := by rw [e2]; rfl
    _ = c (f A u) := by rw [h4]

theorem eq_of_locM {S : Type} [CommRing S] [Algebra K S] {x y : S}
    (h : ∀ (m : Ideal S) (_ : m.IsMaximal), locM K m x = locM K m y) : x = y := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro J hJ
  haveI := hJ
  have hxy := h J hJ
  simp only [locM, IsScalarTower.coe_toAlgHom'] at hxy
  rw [map_sub, hxy, sub_self]

theorem evalWD_of_frChart (h : FrChart pts mapR) : EvalWD pts mapR := by
  intro f hf S _ _ p q φ ψ y z w hy hz
  apply eq_of_locM (K := K)
  intro m hm
  haveI := hm
  obtain ⟨A, u, c, hc⟩ := h S w m
  rw [chartAt_val hf hc hy, chartAt_val hf hc hz]

private theorem evalAt_spec_lemma {f : Rules pts} {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y0 : pts p.R),
      mapR φ y0 y ∧ evalAt pts mapR f y = φ (f p y0) := by
  refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
    hy.choose_spec.choose_spec.choose_spec, ?_⟩
  rw [evalAt, dif_pos hy]

theorem wtAll_of_borChart [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℕ) {f : Rules pts}
    (hf : IsNatural pts mapR f) (hw : IsWeight pts borR e f) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = wchar e t * evalAt pts mapR f y := by
  obtain ⟨p, φ, y0, hm, hv⟩ := evalAt_spec_lemma (f := f) hy
  obtain ⟨p', φ', y0', hm', hv'⟩ := evalAt_spec_lemma (f := f) hy'
  rw [hv, hv']
  apply eq_of_locM (K := K)
  intro m hmax
  haveI := hmax
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hm', chartAt_val hf hc hm]
  calc c' (f A u) = (cB.comp π') (f A u) := by rw [e2]
    _ = cB (f B uB') := by rw [AlgHom.comp_apply, hf A B π' u uB' hπ']
    _ = cB (wchar e tB) * cB (f B uB) := by rw [hw B tB uB uB' hbB, map_mul]
    _ = locM K m (wchar e t) * c (f A u) := by
      have k1 : cB (f B uB) = c (f A u) := by rw [← e1, AlgHom.comp_apply, hf A B π u uB hπ]
      rw [k1]
      simp [wchar, map_prod, map_pow, e3, Units.coe_prod]

end Charts

end Formalism.L2.Pj
