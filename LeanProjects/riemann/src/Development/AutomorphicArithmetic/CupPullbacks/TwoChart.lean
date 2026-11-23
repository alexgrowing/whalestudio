import Development.AutomorphicArithmetic.CupPullbacks.TwoDefs
import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineHomExistsUniqueOfGlobalSection
import Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplicativeGroupHomExistsUniqueOfUnit
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyIsUnitOrIsUnitOfSpanPairEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.EpiFreeBiprodDescOfZariskiLocallySurjective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

noncomputable section
namespace UpperTheory.P2

abbrev tA : Γ(A1, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X

theorem unimodularRow_one_isUnit {A : Type} [CommRing A] (v : Um 1 A) : IsUnit (v.1 0) := by
  have h := v.2
  rw [Set.range_unique] at h
  exact Ideal.span_singleton_eq_top.1 h

theorem span_unit_mul {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (f : A →+* B) (ℓ : Fin M → A)
    (h : Ideal.span (Set.range ℓ) = ⊤) {b : B} (hb : IsUnit b) :
    Ideal.span (Set.range fun i => f (ℓ i) * b) = ⊤ := by
  obtain ⟨u, rfl⟩ := hb
  have h1 : Ideal.map f (Ideal.span (Set.range ℓ)) = ⊤ := by rw [h, Ideal.map_top]
  rw [Ideal.map_span, ← Set.range_comp] at h1
  rw [eq_top_iff, ← h1, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have : (f ∘ ℓ) i = ((↑u⁻¹ : B)) * (f (ℓ i) * u) := by
    simp [mul_comm, mul_assoc]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

def cu {Y : Spc} (c : Y ⟶ Dv 1) {p : ℕ} {T : Scheme.{0}} (y : Sx Y p T) (k : Fin (p + 1)) : Γ(T, ⊤) := (vx (y.map c) k).1 0

theorem cu_unit {Y : Spc} (c : Y ⟶ Dv 1) {p : ℕ} {T : Scheme.{0}} (y : Sx Y p T) (k) : IsUnit (cu c y k) := unimodularRow_one_isUnit _

section Lin
variable {Y : Spc} {S : Scheme.{0}} {M : ℕ} (s : Y ⟶ sch.obj S) (c : Y ⟶ Dv 1) (ℓ : Fin M → Γ(S, ⊤))
  (hℓ : Ideal.span (Set.range ℓ) = ⊤)

def pt {p : ℕ} {T : Scheme.{0}} (y : Sx Y p T) : T ⟶ S := y.map s

theorem pt_along {p r : ℕ} {T : Scheme.{0}} (y : Sx Y r T) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r) :
    pt s (y.along θ) = pt s y := map_along s y θ

theorem pt_res {p : ℕ} {V T : Scheme.{0}} (g : V ⟶ T) (y : Sx Y p T) : pt s (y.res g) = g ≫ pt s y := map_res s g y

theorem cu_along {p r : ℕ} {T : Scheme.{0}} (y : Sx Y r T) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r) (k) :
    cu c (y.along θ) k = cu c y (θ.toOrderHom k) := by
  unfold cu
  rw [map_along, vx_along]

theorem cu_res {p : ℕ} {V T : Scheme.{0}} (g : V ⟶ T) (y : Sx Y p T) (k) : cu c (y.res g) k = g.appTop.hom (cu c y k) := by
  unfold cu
  rw [map_res, vx_res]
  rfl

def linV (T : Scheme.{0}) (y : Sx Y 0 T) : Um M Γ(T, ⊤) :=
  ⟨fun i => (pt s y).appTop.hom (ℓ i) * cu c y 0, span_unit_mul _ ℓ hℓ (cu_unit c y 0)⟩

theorem cu_prop {T : Scheme.{0}} {p : ℕ} (y : Sx Y p T) {i j : Fin (p + 1)} (hij : i ≤ j) :
    ∃ u : Γ(T, ⊤)ˣ, cu c y i = u * cu c y j := by
  obtain ⟨u, hu⟩ := vx_prop (y.map c) hij
  exact ⟨u, congrFun hu 0⟩

def lin : Y ⟶ Dv M :=
  Dv.lift (linV s c ℓ hℓ)
    (fun g y => Subtype.ext (funext fun i => by
      change (pt s (y.res g)).appTop.hom (ℓ i) * cu c (y.res g) 0 = g.appTop.hom ((pt s y).appTop.hom (ℓ i) * cu c y 0)
      rw [pt_res, cu_res, Scheme.Hom.comp_appTop, map_mul]
      rfl))
    (fun T y => by
      obtain ⟨u, hu⟩ := cu_prop c y (Fin.zero_le (1 : Fin 2))
      refine ⟨u, funext fun i => ?_⟩
      have f1 : pt s (y.face 1) = pt s y := pt_along s y _
      have f0 : pt s (y.face 0) = pt s y := pt_along s y _
      have c1 : cu c (y.face 1) 0 = cu c y 0 := cu_along c y (SimplexCategory.δ 1) 0
      have c0 : cu c (y.face 0) 0 = cu c y 1 := cu_along c y (SimplexCategory.δ 0) 0
      change (pt s (y.face 1)).appTop.hom (ℓ i) * cu c (y.face 1) 0 =
        (u : Γ(T, ⊤)) * ((pt s (y.face 0)).appTop.hom (ℓ i) * cu c (y.face 0) 0)
      rw [f1, f0, c1, c0, hu]
      ring)

theorem vx_lin {p : ℕ} {T : Scheme.{0}} (y : Sx Y p T) (k) (i) :
    (vx (y.map (lin s c ℓ hℓ)) k).1 i = (pt s y).appTop.hom (ℓ i) * cu c y k := by
  change (pt s (vtx y k)).appTop.hom (ℓ i) * cu c (vtx y k) 0 = _
  have e1 : pt s (vtx y k) = pt s y := pt_along s y _
  have e2 : cu c (vtx y k) 0 = cu c y k := cu_along c y _ 0
  rw [e1, e2]

end Lin

theorem line_spec {Y : Spc} {N : ℕ} (ℓ : Y ⟶ Dv N) {T : Scheme.{0}} (x : Sx Y 1 T) :
    (vx (x.map ℓ) 0).1 = (lineUnit (ℓ ≫ Dv.line N) x : Γ(T, ⊤)) • (vx (x.map ℓ) 1).1 := by
  let C : ComposableArrows (TU N Γ(T, ⊤)) 1 := x.map ℓ
  have e : lineUnit (ℓ ≫ Dv.line N) x = C.hom.1 := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) C.hom.1) = C.hom.1
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [e]
  exact C.hom.2

section Chart
variable {E : Spc}

abbrev WS (E : Spc) (S : Scheme.{0}) : Spc := (sch.obj S ⨯ E) ⨯ Dv 1

def ps {S : Scheme.{0}} : WS E S ⟶ sch.obj S := prod.fst ≫ prod.fst

def pe {S : Scheme.{0}} : WS E S ⟶ E := prod.fst ≫ prod.snd

def pc {S : Scheme.{0}} : WS E S ⟶ Dv 1 := prod.snd

theorem lineSimplex_ext_of_coordinate {p : ℕ} {T : Scheme.{0}} {x y : Sx (Dv 1) p T} (h : ∀ k, (vx x k).1 0 = (vx y k).1 0) : x = y :=
  vx_ext fun k => Subtype.ext (funext fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h k)

theorem ws_ext {S : Scheme.{0}} {p : ℕ} {T : Scheme.{0}} {x y : Sx (WS E S) p T} (h1 : pt ps x = pt ps y)
    (h2 : x.map pe = y.map pe) (h3 : ∀ k, cu pc x k = cu pc y k) : x = y :=
  prod_sx_ext (prod_sx_ext h1 h2) (lineSimplex_ext_of_coordinate h3)

theorem ws_mk {S : Scheme.{0}} {p : ℕ} {T : Scheme.{0}} (s : T ⟶ S) (e : Sx E p T) (c : Sx (Dv 1) p T) :
    ∃ x : Sx (WS E S) p T, pt ps x = s ∧ x.map pe = e ∧ x.map pc = c := by
  obtain ⟨z, h1, h2⟩ := prod_sx_mk (A := sch.obj S) (p := p) (T := T) s e
  obtain ⟨x, h3, h4⟩ := prod_sx_mk z c
  refine ⟨x, ?_, ?_, h4⟩
  · change (x.map prod.fst).map prod.fst = s
    rw [h3, h1]
  · change (x.map prod.fst).map prod.snd = e
    rw [h3, h2]

def ell (b : Fin 2) : Fin 2 → Γ(A1, ⊤) := fun i => if i = b then 1 else tA

theorem ell_span (b : Fin 2) : Ideal.span (Set.range (ell b)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨b, by simp [ell]⟩) isUnit_one

def gch (b : Fin 2) : WS E A1 ⟶ E ⨯ Dv 2 := prod.lift pe (lin ps pc (ell b) (ell_span b))

theorem vx_gch (b : Fin 2) {p : ℕ} {T : Scheme.{0}} (y : Sx (WS E A1) p T) (k) (i) :
    (vx ((y.map (gch b)).map prod.snd) k).1 i = (pt ps y).appTop.hom (ell b i) * cu pc y k := by
  rw [← map_comp, gch, prod.lift_snd, vx_lin]

theorem gch_pe (b : Fin 2) {p : ℕ} {T : Scheme.{0}} (y : Sx (WS E A1) p T) : (y.map (gch b)).map prod.fst = y.map pe := by
  rw [← map_comp, gch, prod.lift_fst]

theorem vx_gch_self (b : Fin 2) {p : ℕ} {T : Scheme.{0}} (y : Sx (WS E A1) p T) (k) :
    (vx ((y.map (gch b)).map prod.snd) k).1 b = cu pc y k := by
  rw [vx_gch]
  simp [ell]

theorem vx_gch_other (b i : Fin 2) (hi : i ≠ b) {p : ℕ} {T : Scheme.{0}} (y : Sx (WS E A1) p T) (k) :
    (vx ((y.map (gch b)).map prod.snd) k).1 i = (pt ps y).appTop.hom tA * cu pc y k := by
  rw [vx_gch]
  simp [ell, hi]

theorem other (b : Fin 2) : ∃ i : Fin 2, i ≠ b ∧ ∀ j : Fin 2, j = b ∨ j = i := by
  fin_cases b
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

instance gch_mono (b : Fin 2) : Mono (gch (E := E) b) := by
  refine spc_mono _ fun p T x y h => ?_
  have hc : ∀ k, cu pc x k = cu pc y k := by
    intro k
    rw [← vx_gch_self b x k, ← vx_gch_self b y k, h]
  obtain ⟨i, hi, -⟩ := other b
  have ha : (pt ps x).appTop.hom tA = (pt ps y).appTop.hom tA := by
    have := vx_gch_other b i hi x 0
    rw [h, vx_gch_other b i hi y 0, hc 0] at this
    exact ((cu_unit pc y 0).mul_left_inj).1 this.symm
  refine ws_ext ?_ ?_ hc
  · exact (UpperTheory.affineLine_hom_existsUnique_of_globalSection T _).unique rfl ha.symm
  · rw [← gch_pe b x, ← gch_pe b y, h]

theorem gch_sections (b : Fin 2) {p : ℕ} {T : Scheme.{0}} (x : Sx (E ⨯ Dv 2) p T)
    (h : IsUnit ((vx (x.map prod.snd) 0).1 b)) : ∃ y : Sx (WS E A1) p T, y.map (gch b) = x := by
  set v : Fin (p + 1) → Um 2 Γ(T, ⊤) := vx (x.map prod.snd) with hv
  have hp : ∀ k, ∃ u : Γ(T, ⊤)ˣ, (v k).1 = (u : Γ(T, ⊤)) • (v 0).1 := by
    intro k
    obtain ⟨u, hu⟩ := vx_prop (x.map prod.snd) (Fin.zero_le k)
    refine ⟨u⁻¹, ?_⟩
    change (vx (x.map prod.snd) k).1 = _
    rw [show (v 0).1 = _ from hu, smul_smul, Units.inv_mul, one_smul]
  have hu : ∀ k, IsUnit ((v k).1 b) := by
    intro k
    obtain ⟨u, hu⟩ := hp k
    rw [hu]
    exact u.isUnit.mul h
  let cv : Fin (p + 1) → Um 1 Γ(T, ⊤) := fun k => ⟨fun _ => (v k).1 b, by
    rw [Set.range_const, Ideal.span_singleton_eq_top]
    exact hu k⟩
  have hcv : ∀ i j, ∃ u : Γ(T, ⊤)ˣ, (cv i).1 = (u : Γ(T, ⊤)) • (cv j).1 := by
    intro i j
    obtain ⟨a, ha⟩ := hu i
    obtain ⟨c, hc⟩ := hu j
    refine ⟨a * c⁻¹, funext fun _ => ?_⟩
    change (v i).1 b = ((a * c⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) * (v j).1 b
    rw [← ha, ← hc, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  obtain ⟨w, hw⟩ := h
  obtain ⟨i, hi, hall⟩ := other b
  obtain ⟨s, hs, -⟩ := UpperTheory.affineLine_hom_existsUnique_of_globalSection T ((v 0).1 i * ((w⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤)))
  obtain ⟨y, h1, h2, h3⟩ := ws_mk (E := E) s (x.map prod.fst) (Dv.mk cv hcv)
  refine ⟨y, prod_sx_ext ?_ (vx_ext fun k => Subtype.ext (funext fun j => ?_))⟩
  · rw [gch_pe, h2]
  · have hck : cu pc y k = (v k).1 b := by
      unfold cu
      rw [h3]
      rfl
    rcases hall j with rfl | rfl
    · rw [vx_gch_self, hck]
    · rw [vx_gch_other _ _ hi, hck, h1, hs]
      obtain ⟨u, hu'⟩ := hp k
      change _ = (v k).1 j
      rw [hu']
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hw]
      calc (v 0).1 j * ((w⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) * ((u : Γ(T, ⊤)) * (w : Γ(T, ⊤)))
          = (u : Γ(T, ⊤)) * (v 0).1 j * (((w⁻¹ : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) * (w : Γ(T, ⊤))) := by ring
        _ = _ := by rw [Units.inv_mul, mul_one]

theorem span_pair {A : Type} [CommRing A] (v : Um 2 A) : Ideal.span {v.1 0, v.1 1} = ⊤ := by
  have h := v.2
  rwa [show Set.range v.1 = {v.1 0, v.1 1} from ?_] at h
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem gch_loc {p : ℕ} {U : Scheme.{0}} (y : Sx (E ⨯ Dv 2) p U) :
    Loc U fun V g => (∃ z : Sx (WS E A1) p V, z.map (gch 0) = y.res g) ∨ ∃ z : Sx (WS E A1) p V, z.map (gch 1) = y.res g := by
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_isUnit_or_isUnit_of_span_pair_eq_top U _ _ (span_pair (vx (y.map prod.snd) 0))
  refine ⟨S, hS, fun V g hg => ?_⟩
  have key : ∀ b : Fin 2, IsUnit (g.appTop.hom ((vx (y.map prod.snd) 0).1 b)) →
      ∃ z : Sx (WS E A1) p V, z.map (gch b) = y.res g := by
    intro b hb
    refine gch_sections b _ ?_
    rw [map_res, vx_res]
    exact hb
  rcases hP V g hg with h | h
  · exact Or.inl (key 0 h)
  · exact Or.inr (key 1 h)

theorem gch_cover (R : Type) [CommRing R] : Cover2 R (gch (E := E) 0) (gch (E := E) 1) :=
  ⟨inferInstance, inferInstance, fun n => UpperTheory.epi_freeBiprodDesc_of_zariskiLocally_surjective R _ _ fun U y => gch_loc (p := n.unop.len) y⟩

def wc {S : Scheme.{0}} (T : Scheme.{0}) (y : Sx (WS E S) 0 T) : (Γ(T, ⊤))ˣ := (cu_unit pc y 0).unit

theorem wc_val {S : Scheme.{0}} (T : Scheme.{0}) (y : Sx (WS E S) 0 T) : (wc T y : Γ(T, ⊤)) = cu pc y 0 := rfl

theorem gch_triv (b : Fin 2) : IsTrivBy ((gch (E := E) b ≫ prod.snd) ≫ Dv.line 2) wc := by
  refine ⟨fun {T' T} g x => Units.ext ?_, fun T x => Units.ext ?_⟩
  · change cu pc (x.res g) 0 = g.appTop.hom (cu pc x 0)
    exact cu_res pc g x 0
  · have h := congrFun (line_spec (gch (E := E) b ≫ prod.snd) x) b
    have e0 : (vx (x.map (gch b ≫ prod.snd)) 0).1 b = cu pc x 0 := vx_gch_self b x 0
    have e1 : (vx (x.map (gch b ≫ prod.snd)) 1).1 b = cu pc x 1 := vx_gch_self b x 1
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [e0, e1] at h
    rw [Units.val_mul, wc_val, wc_val]
    have c1 : cu pc (x.face 1) 0 = cu pc x 0 := cu_along pc x (SimplexCategory.δ 1) 0
    have c0 : cu pc (x.face 0) 0 = cu pc x 1 := cu_along pc x (SimplexCategory.δ 0) 0
    rw [c1, c0, h]

def affineLineMorphismOfSection {T : Scheme.{0}} (a : Γ(T, ⊤)) : T ⟶ A1 := (UpperTheory.affineLine_hom_existsUnique_of_globalSection T a).exists.choose

theorem affineLineMorphismOfSection_coordinate {T : Scheme.{0}} (a : Γ(T, ⊤)) : (affineLineMorphismOfSection a).appTop.hom tA = a := (UpperTheory.affineLine_hom_existsUnique_of_globalSection T a).exists.choose_spec

theorem affineLine_hom_ext {T : Scheme.{0}} {s s' : T ⟶ A1} (h : s.appTop.hom tA = s'.appTop.hom tA) : s = s' :=
  (UpperTheory.affineLine_hom_existsUnique_of_globalSection T _).unique rfl h.symm

def mkW {Y : Spc} {S : Scheme.{0}} (s : Y ⟶ sch.obj S) (e : Y ⟶ E) (c : Y ⟶ Dv 1) : Y ⟶ WS E S := prod.lift (prod.lift s e) c

@[simp] theorem mkW_ps {Y : Spc} {S : Scheme.{0}} (s : Y ⟶ sch.obj S) (e : Y ⟶ E) (c : Y ⟶ Dv 1) : mkW s e c ≫ ps = s := by
  rw [mkW, ps, ← Category.assoc, prod.lift_fst, prod.lift_fst]

@[simp] theorem mkW_pe {Y : Spc} {S : Scheme.{0}} (s : Y ⟶ sch.obj S) (e : Y ⟶ E) (c : Y ⟶ Dv 1) : mkW s e c ≫ pe = e := by
  rw [mkW, pe, ← Category.assoc, prod.lift_fst, prod.lift_snd]

@[simp] theorem mkW_pc {Y : Spc} {S : Scheme.{0}} (s : Y ⟶ sch.obj S) (e : Y ⟶ E) (c : Y ⟶ Dv 1) : mkW s e c ≫ pc = c := by
  rw [mkW, pc, prod.lift_snd]

section Overlap
variable (q : ℕ) [NeZero q]

def jA : Gq q ⟶ A1 := affineLineMorphismOfSection ((tq q : (Γ(Gq q, ⊤))ˣ) : Γ(Gq q, ⊤))

def jB : Gq q ⟶ A1 := affineLineMorphismOfSection (((tq q)⁻¹ : (Γ(Gq q, ⊤))ˣ) : Γ(Gq q, ⊤))

def tv {p : ℕ} {T : Scheme.{0}} (y : Sx (WS E (Gq q)) p T) : (Γ(T, ⊤))ˣ :=
  Units.map (pt ps y).appTop.hom.toMonoidHom (tq q)

theorem tq_span : Ideal.span (Set.range fun _ : Fin 1 => ((tq q : (Γ(Gq q, ⊤))ˣ) : Γ(Gq q, ⊤))) = ⊤ := by
  rw [Set.range_const, Ideal.span_singleton_eq_top]
  exact (tq q).isUnit

def cA : WS E (Gq q) ⟶ WS E A1 :=
  mkW (ps ≫ sch.map (jB q)) pe (lin ps pc (fun _ => ((tq q : (Γ(Gq q, ⊤))ˣ) : Γ(Gq q, ⊤))) (tq_span q))

def cB : WS E (Gq q) ⟶ WS E A1 := mkW (ps ≫ sch.map (jA q)) pe pc

variable {q}
variable {p : ℕ} {T : Scheme.{0}} (y : Sx (WS E (Gq q)) p T)

theorem pe_cA : (y.map (cA q)).map pe = y.map pe := by
  rw [← map_comp, cA, mkW_pe]

theorem pe_cB : (y.map (cB q)).map pe = y.map pe := by
  rw [← map_comp, cB, mkW_pe]

theorem a_cA : (pt ps (y.map (cA q))).appTop.hom tA = ((tv q y)⁻¹ : (Γ(T, ⊤))ˣ) := by
  have e : pt ps (y.map (cA q)) = pt ps y ≫ jB q := by
    change y.map (cA q ≫ ps) = _
    rw [cA, mkW_ps]
    rfl
  rw [e, Scheme.Hom.comp_appTop]
  change (pt ps y).appTop.hom ((jB q).appTop.hom tA) = _
  rw [jB, affineLineMorphismOfSection_coordinate]
  rfl

theorem a_cB : (pt ps (y.map (cB q))).appTop.hom tA = (tv q y : (Γ(T, ⊤))ˣ) := by
  have e : pt ps (y.map (cB q)) = pt ps y ≫ jA q := by
    change y.map (cB q ≫ ps) = _
    rw [cB, mkW_ps]
    rfl
  rw [e, Scheme.Hom.comp_appTop]
  change (pt ps y).appTop.hom ((jA q).appTop.hom tA) = _
  rw [jA, affineLineMorphismOfSection_coordinate]
  rfl

theorem cu_cA (k) : cu pc (y.map (cA q)) k = (tv q y : (Γ(T, ⊤))ˣ) * cu pc y k := by
  change (vx (y.map (cA q ≫ pc)) k).1 0 = _
  rw [cA, mkW_pc, vx_lin]
  rfl

theorem cu_cB (k) : cu pc (y.map (cB q)) k = cu pc y k := by
  change (vx (y.map (cB q ≫ pc)) k).1 0 = _
  rw [cB, mkW_pc]
  rfl

theorem over_w : cA (E := E) q ≫ gch 0 = cB q ≫ gch 1 := by
  refine spc_hom_ext fun p T x => ?_
  change (x.map (cA q)).map (gch 0) = (x.map (cB q)).map (gch 1)
  refine prod_sx_ext ?_ (vx_ext fun k => Subtype.ext (funext fun i => ?_))
  · rw [gch_pe, gch_pe, pe_cA, pe_cB]
  · fin_cases i
    · change (vx (((x.map (cA q)).map (gch 0)).map prod.snd) k).1 0 = (vx (((x.map (cB q)).map (gch 1)).map prod.snd) k).1 0
      rw [vx_gch_self, vx_gch_other 1 0 (by decide), a_cB, cu_cA, cu_cB]
    · change (vx (((x.map (cA q)).map (gch 0)).map prod.snd) k).1 1 = (vx (((x.map (cB q)).map (gch 1)).map prod.snd) k).1 1
      rw [vx_gch_self, vx_gch_other 0 1 (by decide), a_cA, cu_cA, cu_cB, ← mul_assoc, Units.inv_mul, one_mul]

theorem q_unit (hE : Inv q E) {p : ℕ} {T : Scheme.{0}} (e : Sx E p T) : IsUnit ((q : ℕ) : Γ(T, ⊤)) :=
  hE T ⟨vtx e 0⟩

theorem over_pullback (hE : Inv q E) : IsPullback (cA (E := E) q) (cB q) (gch 0) (gch 1) := by
  refine isPullback_of_sx (over_w) ?_ ?_
  · intro p T x x' h1 h2
    have hc : ∀ k, cu pc x k = cu pc x' k := by
      intro k
      rw [← cu_cB x k, ← cu_cB x' k, h2]
    have ht : tv q x = tv q x' := by
      apply Units.ext
      rw [← a_cB x, ← a_cB x', h2]
    refine ws_ext ?_ ?_ hc
    · exact (UpperTheory.multiplicativeGroup_hom_existsUnique_of_unit q T (q_unit hE (x.map pe)) (tv q x)).unique rfl ht.symm
    · rw [← pe_cB x, ← pe_cB x', h2]
  · intro p T s t h
    have he : s.map pe = t.map pe := by
      rw [← gch_pe 0 s, ← gch_pe 1 t, h]
    have h0 : ∀ k, cu pc s k = (pt ps t).appTop.hom tA * cu pc t k := by
      intro k
      rw [← vx_gch_self 0 s k, h, vx_gch_other 1 0 (by decide)]
    have h1 : ∀ k, (pt ps s).appTop.hom tA * cu pc s k = cu pc t k := by
      intro k
      rw [← vx_gch_other 0 1 (by decide) s k, h, vx_gch_self]
    have hst : (pt ps s).appTop.hom tA * (pt ps t).appTop.hom tA = 1 := by
      have := h1 0
      rw [h0 0, ← mul_assoc] at this
      exact (cu_unit pc t 0).mul_left_inj.1 (this.trans (one_mul _).symm)
    let τ : (Γ(T, ⊤))ˣ := ⟨(pt ps t).appTop.hom tA, (pt ps s).appTop.hom tA, by rw [mul_comm]; exact hst, hst⟩
    obtain ⟨sτ, hτ, -⟩ := UpperTheory.multiplicativeGroup_hom_existsUnique_of_unit q T (q_unit hE (t.map pe)) τ
    obtain ⟨x, e1, e2, e3⟩ := ws_mk (E := E) sτ (t.map pe) (t.map pc)
    have htv : tv q x = τ := by
      unfold tv
      rw [e1, hτ]
    have hcu : ∀ k, cu pc x k = cu pc t k := by
      intro k
      unfold cu
      rw [e3]
    refine ⟨x, ws_ext ?_ ?_ ?_, ws_ext ?_ ?_ ?_⟩
    · exact affineLine_hom_ext (by rw [a_cA, htv]; rfl)
    · rw [pe_cA, e2, he]
    · intro k
      rw [cu_cA, htv, hcu, h0]
    · exact affineLine_hom_ext (by rw [a_cB, htv])
    · rw [pe_cB, e2]
    · intro k
      rw [cu_cB, hcu]

end Overlap
end Chart

end UpperTheory.P2
end
