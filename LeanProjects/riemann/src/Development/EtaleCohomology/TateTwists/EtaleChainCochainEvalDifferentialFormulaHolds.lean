import Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationCoboundaryFormula

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvDeltaPf

variable {R : Type} [CommRing R]

def secHom {F G : Shv R} (U : Scheme.{0}) (x : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := Sec.map φ x
  map_zero' := by simp [Sec.map]
  map_add' f g := by simp [Sec.map]

lemma sec_zsmul {F G : Shv R} (f : F ⟶ G) (c : ℤ) (U : Scheme.{0}) (x : Sec F U) : Sec.map (c • f) x = c • Sec.map f x :=
  map_zsmul (secHom (G := G) U x) c f

lemma sec_sum {ι : Type} (s : Finset ι) {F G : Shv R} (f : ι → (F ⟶ G)) (U : Scheme.{0}) (x : Sec F U) : Sec.map (∑ i ∈ s, f i) x = ∑ i ∈ s, Sec.map (f i) x :=
  map_sum (secHom (G := G) U x) f s

variable (R) in
lemma freeGen_map {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) : Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  calc _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ sheafifyMap Scheme.etaleTopology ((freeP R).map f)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := rfl
    _ = (((freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) := by rw [toSheafify_naturality]
    _ = ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) := rfl
    _ = _ := by
      unfold freeGen
      congr 1
      simp [freeP, ModuleCat.freeMk]
      exact Finsupp.mapDomain_single

variable (R) in
lemma chains_d (E : Spc) (p : ℕ) : (chainsXIso R E (p+1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  have h1 : ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) = (chainsXIso R E (p+1)).hom ≫ ((chainsN R).obj E).d (p+1) p ≫ (chainsXIso R E p).inv :=
    HomologicalComplex.extend_d_eq _ _ rfl rfl
  have h2 : ((chainsN R).obj E).d (p+1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
    simp [chainsN]
    rfl
  rw [h1, h2, Iso.inv_hom_id_assoc]
  rfl

variable (R) in
lemma etale_simplicial_chains_isZero_of_positive_degree (E : Spc) (k : ℤ) (hk : 0 < k) : IsZero (((chains R).obj E).X k) :=
  HomologicalComplex.isZero_extend_X _ _ _ (by rintro i (h : -(i:ℤ) = k); omega)

lemma sec_add {F G : Shv R} (f g : F ⟶ G) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
  map_add (secHom (G := G) U x) f g

lemma sec_comp {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) : Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem part0 {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (x : Sx E 0 U) : ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
  have hz : ((chains R).obj E).d (-((0:ℕ):ℤ)) (-((0:ℕ):ℤ) + 1) = 0 := (etale_simplicial_chains_isZero_of_positive_degree R E _ (by omega)).eq_of_tgt _ _
  have key : (chainsXIso R E 0).inv ≫ (δ n m α).v (-((0:ℕ):ℤ)) m (by simp) = ((chainsXIso R E 0).inv ≫ α.v (-((0:ℕ):ℤ)) n (by simp)) ≫ I.d n m := by
    rw [δ_v n m hm α _ _ (by simp) n (-((0:ℕ):ℤ) + 1) (by omega) rfl, hz]
    simp
  show Sec.map (_ ≫ _) _ = _
  rw [key]
  rfl

theorem partS {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) : ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  have key : (chainsXIso R E (p+1)).inv ≫ (δ n m α).v _ t ht = ((chainsXIso R E (p+1)).inv ≫ α.v _ s hs) ≫ I.d s t + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ((free R).map (E.δ i) ≫ ((chainsXIso R E p).inv ≫ α.v (-(p:ℤ)) t (by omega))) := by
    rw [δ_v n m hm α _ _ ht s (-(p:ℤ)) (by omega) (by push_cast; ring), Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ← Category.assoc, chains_d]
    simp only [Category.assoc, Preadditive.sum_comp, Linear.smul_comp]
  show Sec.map (_ ≫ _) _ = _
  rw [key, Units.smul_def, Units.smul_def, sec_add, sec_zsmul, sec_sum]
  refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [sec_zsmul, sec_comp, freeGen_map]
  rfl

end LateralTheory.EtaleFoundations.EvDeltaPf

theorem LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds : LateralTheory.EtaleFoundations.EtaleCochainEvaluationCoboundaryFormula := by
  intro R _ E I n m hm α U
  exact ⟨fun x => LateralTheory.EtaleFoundations.EvDeltaPf.part0 hm α U x,
    fun p s t hs ht x => LateralTheory.EtaleFoundations.EvDeltaPf.partS hm α U p s t hs ht x⟩
