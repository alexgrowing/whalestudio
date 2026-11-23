import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory.ConeLoc

open CochainComplex.mappingCone

private theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W t => P' W (t ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => k V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), ?_, ?_⟩
  · exact GrothendieckTopology.bind_covering _ hS (fun V g hg => hT V g hg)
  · rintro W t ⟨V, e, g, hg, he, rfl⟩
    exact hT' V g hg W e he

private theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => k V g (hP V g hg)⟩

section
variable {R : Type} [CommRing R]

private theorem sm_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

private theorem sm_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ + ψ) a = Sec.map φ a + Sec.map ψ a := rfl

private theorem sm_sub {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ - ψ) a = Sec.map φ a - Sec.map ψ a := rfl

private theorem sm_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (-φ) a = - Sec.map φ a := rfl

private theorem sm_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have hn := φ.hom.naturality g.op
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hn]

private theorem ms_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem ms_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

private theorem ms_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b :=
  map_sub (φ.hom.app (op U)).hom a b

private theorem ms_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map φ (-a) = - Sec.map φ a :=
  map_neg (φ.hom.app (op U)).hom a

private theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ a b

private theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

private theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (h ≫ g) a = Sec.res h (Sec.res g a) := by
  simp [Sec.res]

end

variable {K M : Cx ℤ} (φ : K ⟶ M)

private theorem fst_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((fst φ).1.v j k hjk) (Sec.map ((mappingCone φ).d i j) s) =
      - Sec.map (K.d j k) (Sec.map ((fst φ).1.v i j hij) s) := by
  rw [← sm_comp, d_fst_v φ i j k hij hjk, sm_neg, sm_comp]

private theorem snd_d (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((snd φ).v j j (add_zero _)) (Sec.map ((mappingCone φ).d i j) s) =
      Sec.map (φ.f j) (Sec.map ((fst φ).1.v i j hij) s) + Sec.map (M.d i j) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  rw [← sm_comp, d_snd_v φ i j hij, sm_add, sm_comp, sm_comp]

private theorem decomp (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    s = Sec.map ((inl φ).v j i (by omega)) (Sec.map ((fst φ).1.v i j hij) s) +
      Sec.map ((inr φ).f i) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  have hid := id_X φ i j hij
  calc s = Sec.map (𝟙 _) s := rfl
    _ = _ := by rw [← hid]; rfl

private theorem d_inl (n : ℤ) {T : Scheme.{0}} (a : Sec (K.X n) T) (ha : Sec.map (K.d n (n + 1)) a = 0) :
    Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) := by
  rw [← sm_comp, inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, ha, ms_zero, sub_zero]

private theorem d_inr (i j : ℤ) {T : Scheme.{0}} (c : Sec (M.X i) T) :
    Sec.map ((mappingCone φ).d i j) (Sec.map ((inr φ).f i) c) = Sec.map ((inr φ).f j) (Sec.map (M.d i j) c) := by
  rw [← sm_comp, inr_f_d, sm_comp]

private theorem core (Q : Scheme.{0} → Prop) (hQ : ∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V)
    (H1 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (M.X n) T), Sec.map (M.d n (n + 1)) b = 0 →
      Loc T fun V g => ∃ (a : Sec (K.X n) V) (c : Sec (M.X (n - 1)) V), Sec.map (K.d n (n + 1)) a = 0 ∧
        Sec.map (φ.f n) a = Sec.res g b + Sec.map (M.d (n - 1) n) c)
    (H2 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (K.X n) T), Sec.map (K.d n (n + 1)) a = 0 →
      (∃ c : Sec (M.X (n - 1)) T, Sec.map (φ.f n) a = Sec.map (M.d (n - 1) n) c) →
      Loc T fun V g => ∃ a' : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) a' = Sec.res g a)
    (U : Scheme.{0}) (hU : Q U) (n : ℤ) (b : Sec ((mappingCone φ).X n) U)
    (hb : Sec.map ((mappingCone φ).d n (n + 1)) b = 0) :
    Loc U fun V g => ∃ c : Sec ((mappingCone φ).X (n - 1)) V,
      Sec.map ((mappingCone φ).d (n - 1) n) c = Sec.res g b := by
  have hdec := decomp φ n (n + 1) rfl b
  have hfd := fst_d φ n (n + 1) (n + 1 + 1) rfl rfl b
  have hsd := snd_d φ n (n + 1) rfl b
  set x := Sec.map ((fst φ).1.v n (n + 1) rfl) b with hx
  set y := Sec.map ((snd φ).v n n (add_zero n)) b with hy
  have hxd : Sec.map (K.d (n + 1) (n + 1 + 1)) x = 0 := by
    rw [hb, ms_zero] at hfd
    exact neg_eq_zero.mp hfd.symm
  have hxy : Sec.map (φ.f (n + 1)) x + Sec.map (M.d n (n + 1)) y = 0 := by
    rw [hb, ms_zero] at hsd
    exact hsd.symm
  have hyx : Sec.map (M.d n (n + 1)) y + Sec.map (φ.f (n + 1)) x = 0 := (add_comm _ _).trans hxy
  have hcob : ∃ c : Sec (M.X (n + 1 - 1)) U,
      Sec.map (φ.f (n + 1)) x = Sec.map (M.d (n + 1 - 1) (n + 1)) c := by
    refine ⟨Sec.map (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (-y), ?_⟩
    rw [← sm_comp (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (M.d (n + 1 - 1) (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ms_neg]
    exact eq_neg_of_add_eq_zero_left hxy
  apply loc_bind (H2 U hU (n + 1) x hxd hcob)
  rintro V g ⟨a', ha'⟩
  set a := Sec.map (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom a' with ha
  have had : Sec.map (K.d n (n + 1)) a = Sec.res g x := by
    rw [ha, ← sm_comp (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom (K.d n (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ha']
  set y' := Sec.res g y + Sec.map (φ.f n) a with hy'
  have hy'd : Sec.map (M.d n (n + 1)) y' = 0 := by
    rw [hy', ms_add, ← sm_res, ← sm_comp (φ.f n) (M.d n (n + 1)), φ.comm n (n + 1), sm_comp, had,
      ← sm_res, ← res_add, hyx, res_zero]
  have hdc1 : Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) - Sec.map ((inl φ).v (n + 1) n (by omega)) (Sec.res g x) := by
    rw [← sm_comp ((inl φ).v n (n - 1) (by omega)) ((mappingCone φ).d (n - 1) n),
      inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, had]
  apply loc_mono (H1 V (hQ g hU) n y' hy'd)
  rintro W t ⟨a₂, c₂, ha₂, hφ⟩
  refine ⟨Sec.map ((inl φ).v n (n - 1) (by omega)) a₂ - Sec.map ((inr φ).f (n - 1)) c₂ -
    Sec.res t (Sec.map ((inl φ).v n (n - 1) (by omega)) a), ?_⟩
  rw [res_comp, hdec, ms_sub, ms_sub, d_inl φ n a₂ ha₂, d_inr, ← sm_res, hdc1, hφ, hy']
  simp only [sm_res, res_add, map_sub, map_add]
  abel

end UpperTheory.ConeLoc

theorem UpperTheory.bijective_semiMap_of_locally_surjective_on_cocycles :
    ∀ (R : Type) [CommRing R] (L B : Cx R) (ρ : SemiMap L B) (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (B.X n) T), Sec.map (B.d n (n + 1)) b = 0 →
          Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (B.X (n - 1)) V), Sec.map (L.d n (n + 1)) a = 0 ∧
            ρ.app V n a = Sec.res g b + Sec.map (B.d (n - 1) n) c) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
          (∃ c : Sec (B.X (n - 1)) T, ρ.app T n a = Sec.map (B.d (n - 1) n) c) →
          Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) →
        ∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec ((mappingCone ρ.toZ).X n) U), Sec.map ((mappingCone ρ.toZ).d n (n + 1)) b = 0 →
          Loc U fun V g => ∃ c : Sec ((mappingCone ρ.toZ).X (n - 1)) V, Sec.map ((mappingCone ρ.toZ).d (n - 1) n) c = Sec.res g b := by
  intro R _ L B ρ Q hQ H1 H2 U hU n b hb
  exact UpperTheory.ConeLoc.core ρ.toZ Q hQ (fun T hT m c hc => H1 T hT m c hc)
    (fun T hT m a ha hc => H2 T hT m a ha hc) U hU n b hb
