import Development.EtaleCohomology.EtaleSheaves.EtaleChapterESix

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.t_E6Cut

def ConnK (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, (n < c - 1 → Function.Bijective (HK.pull R f F n)) ∧ (n < c → Function.Injective (HK.pull R f F n))

def Conn (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') : Prop := ConnK R F c ((chains R).map f)

def EtLoc (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop) : Prop :=
  ∃ S ∈ Scheme.etaleTopology.{0} T, ∀ (V : Scheme.{0}) (k : V ⟶ T), S k → P V k

def sxMap {E E' : Spc} (f : E ⟶ E') {p : ℕ} {T : Scheme.{0}} (x : Sx E p T) : Sx E' p T :=
  (f.app (op (SimplexCategory.mk p))).app (op T) x

def sxRes {E : Spc} {p : ℕ} {V T : Scheme.{0}} (k : V ⟶ T) (x : Sx E p T) : Sx E p V :=
  (E.obj (op (SimplexCategory.mk p))).map k.op x

def QIso {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B) : Prop :=
  Function.Bijective (Ideal.quotientMap (I.map α) α Ideal.le_comap_map)

def varIdeal {d : ℕ} {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B) : Ideal B :=
  Ideal.span (Set.range fun j => φ (MvPolynomial.X j))

def IsCompl' {B : Type} [CommRing B] (I : Ideal B) (U : (Spec (CommRingCat.of B)).Opens) : Prop :=
  ∀ x : Spec (CommRingCat.of B), x ∈ U ↔ ¬ I ≤ (show PrimeSpectrum B from x).asIdeal

def LeafRel : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L),
  ConnK R F c f ↔ ∀ n < c, Subsingleton (HK R (mappingCone f) F n)

def LeafLevel : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E'),
  (∀ p : ℕ, Conn R F (c - p) (disc.map (f.app (op (SimplexCategory.mk p))))) → Conn R F c f

def LeafProd : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {Y : Scheme.{0}} {ι : Type} (V : ι → Scheme.{0})
  (j : ∀ a, V a ⟶ Y) [∀ a, IsOpenImmersion (j a)], (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) →
  (∀ y : Y, ∃ a, y ∈ Set.range (j a)) → ∀ n : ℤ,
  Function.Bijective fun (x : H R (sch.obj Y) F n) (a : ι) => pull R (sch.map (j a)) F n x

def LeafLoc : Prop := A1 → A2 → A9 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} (U : X.Opens),
  (∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
    x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι)) →
  Conn R F c (sch.map U.ι)

def LeafExc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {U E' E : Spc} (f : U ⟶ E) [Mono f] (g : E' ⟶ E),
  (∀ (p : ℕ) (T : Scheme.{0}) (y : Sx E p T), EtLoc T fun V k =>
    (∃ u : Sx U p V, sxMap f u = sxRes k y) ∨ ∃ a : Sx E' p V, sxMap g a = sxRes k y) →
  (∀ (p : ℕ) (T : Scheme.{0}) (a b : Sx E' p T), sxMap g a = sxMap g b → EtLoc T fun V k =>
    sxRes k a = sxRes k b ∨ ∃ u : Sx U p V, sxMap f u = sxRes k (sxMap g a)) →
  (Conn R F c f ↔ Conn R F c (pullback.snd f g))

def LeafExcRing : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {B W : Type} [CommRing B] [CommRing W]
  (α : B →+* W) (I : Ideal B), α.Etale → QIso α I → ∀ (U : (Spec (CommRingCat.of B)).Opens)
  (U' : (Spec (CommRingCat.of W)).Opens), IsCompl' I U → IsCompl' (I.map α) U' →
  (Conn R F c (sch.map U.ι) ↔ Conn R F c (sch.map U'.ι))

def LeafRoof : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ∃ (D W : Type) (_ : CommRing D) (_ : CommRing W) (_ : B →+* D) (α : B →+* W) (β : MvPolynomial (Fin d) D →+* W),
    α.Etale ∧ β.Etale ∧ (∀ j, α (φ (MvPolynomial.X j)) = β (MvPolynomial.X j)) ∧ QIso α (varIdeal φ) ∧
    QIso β (varIdeal (RingHom.id (MvPolynomial (Fin d) D)))

def LeafChartRing : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ g ∉ P, ∃ (C : Type) (_ : CommRing C)
    (φ : MvPolynomial (Fin d) C →+* Localization.Away g), φ.Etale ∧ I.map (algebraMap B _) = varIdeal φ

def LeafChart : Prop := ∀ {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)] (x : X), x ∈ Set.range ι →
  ∀ W : X.Opens, x ∈ W → ∃ (B C : Type) (_ : CommRing B) (_ : CommRing C) (j : Spec (CommRingCat.of B) ⟶ X)
    (_ : IsOpenImmersion j) (φ : MvPolynomial (Fin d) C →+* B), φ.Etale ∧ x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧
    ∀ y : Spec (CommRingCat.of B), j y ∈ Set.range ι ↔ varIdeal φ ≤ (show PrimeSpectrum B from y).asIdeal

def LeafNat : Prop := A1 → A5 → A7 → A9 → A10 → DivisorNaturality

def LeafProj : Prop := A1 → A5 → A7 → A9 → A10 → D1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {E : Spc} {N : ℕ}
  (V : E ⟶ ofCat (glCat N)) (V' : E ⟶ ofCat (glCat (N + 1))), Inv q E →
  ∀ s : pullback V (PGL.pr N) ⟶ pullback V' (PGL.pr (N + 1)), s ≫ pullback.fst _ _ = pullback.fst _ _ →
    s ≫ pullback.snd _ _ ≫ PGL.line (N + 1) = pullback.snd _ _ ≫ PGL.line N → Conn _ (tw q i) (2 * N) s

def LeafHI : Prop := B3 → C4 → ∀ (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}), IsUnit (q : Γ(X, ⊤)) →
  Eqv _ (sch.map (𝔸(Fin 1; X) ↘ X)) (tw q i)

def LeafAff : Prop := A1 → A3 → A5 → A7 → A9 → A10 → B3 → C4 → D1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) (d : ℕ) (D : Type)
  [CommRing D], IsUnit (q : D) → ∀ U : (Spec (CommRingCat.of (MvPolynomial (Fin d) D))).Opens,
  IsCompl' (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U → Conn _ (tw q i) (2 * d) (sch.map U.ι)

theorem exists_compl {B : Type} [CommRing B] (I : Ideal B) : ∃ U, IsCompl' I U :=
  ⟨⟨(PrimeSpectrum.zeroLocus (I : Set B))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩, fun _ => Iff.rfl⟩

theorem map_varIdeal {d : ℕ} {C B W : Type} [CommRing C] [CommRing B] [CommRing W] (φ : MvPolynomial (Fin d) C →+* B)
    (α : B →+* W) : (varIdeal φ).map α = Ideal.span (Set.range fun j => α (φ (MvPolynomial.X j))) := by
  rw [varIdeal, Ideal.map_span, ← Set.range_comp]; rfl

theorem goal_of (hLoc : LeafLoc) (hExc : LeafExcRing) (hRoof : LeafRoof) (hChart : LeafChart) (hAff : LeafAff) :
    LateralTheory.E.EtaleChapterESix := by
  intro a1 a2 a3 _ a5 a7 _ a9 a10 _ _ _ b3 _ _ _ _ _ _ c4 _ d1 _ _ _ _ _ _ q _ X Z S p ι _ d e _ _ hq U hU n i
  refine hLoc a1 a2 a9 _ (tw q i) (2 * d) U (fun x hx W hW => ?_) n
  have hmem : ∀ y : X, y ∈ U ↔ y ∉ Set.range ι := fun y => by
    change y ∈ (U : Set X) ↔ _
    rw [hU]; rfl
  obtain ⟨B, C, _, _, j, hj, φ, hφ, hxj, hjW, hz⟩ := hChart p ι d e x (by by_contra h; exact hx ((hmem x).2 h)) W hW
  refine ⟨_, j, hj, hxj, hjW, ?_⟩
  obtain ⟨D, W', _, _, ψ, α, β, hα, hβ, hc, qα, qβ⟩ := hRoof d φ hφ
  have hqB : IsUnit (q : B) := by
    simpa using hq.map ((j ≫ p).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom
  have hqD : IsUnit (q : D) := by simpa using hqB.map ψ
  obtain ⟨U', hU'⟩ := exists_compl ((varIdeal φ).map α)
  obtain ⟨U₀, hU₀⟩ := exists_compl (varIdeal (RingHom.id (MvPolynomial (Fin d) D)))
  have he : (varIdeal (RingHom.id (MvPolynomial (Fin d) D))).map β = (varIdeal φ).map α := by
    rw [map_varIdeal, map_varIdeal]
    simp only [hc, RingHom.id_apply]
  have h1 := (hExc a1 _ (tw q i) (2 * d) β _ hβ qβ U₀ U' hU₀ (he ▸ hU')).1
    (hAff a1 a3 a5 a7 a9 a10 b3 c4 d1 q i d D hqD U₀ hU₀)
  refine (hExc a1 _ (tw q i) (2 * d) α _ hα qα _ U' (fun y => ?_) hU').2 h1
  exact (hmem (j y)).trans (not_congr (hz y))

end LateralTheory.E.t_E6Cut
