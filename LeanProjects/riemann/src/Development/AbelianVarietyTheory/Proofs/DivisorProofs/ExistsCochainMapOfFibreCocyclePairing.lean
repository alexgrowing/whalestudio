import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC.PsiModel
variable {R : Type} [CommRing R]

theorem map_sres {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sx.map f (Sx.res g x) = Sx.res g (Sx.map f x) := by
  unfold Sx.map Sx.res
  exact NatTrans.naturality_apply (f.app (op (SimplexCategory.mk p))) g.op x

theorem map_face {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    Sx.map f (Sx.face x i) = Sx.face (Sx.map f x) i := by
  unfold Sx.map Sx.face
  have h1 := NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)
  simp only [NatTrans.comp_app] at h1
  have h2 := ConcreteCategory.congr_hom h1 x
  simp only [ConcreteCategory.comp_apply] at h2
  exact h2

theorem map_map {E E' E'' : Spc} (f : E ⟶ E') (f' : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map f' (Sx.map f x) = Sx.map (f ≫ f') x := rfl

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp [Sec.res]

theorem ev_smul {E : Spc} {I : Cx R} {n : ℤ} (r : ULift.{1} R) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (r • α) p s h U x = r • ev α p s h U x := by
  rw [ev_def, ev_def, Cochain.smul_v, Linear.comp_smul]
  rfl

variable {q N : ℕ}

def fstH {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) p V) : V ⟶ U :=
  Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y

theorem fstH_res {U V' V : Scheme.{0}} {p : ℕ} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    fstH (Sx.res g y) = g ≫ fstH y := by
  unfold fstH
  rw [map_sres]
  rfl

theorem fstH_face {U V : Scheme.{0}} {p : ℕ} (y : Sx (sch.obj U ⨯ fibQ q N) (p + 1) V) (i : Fin (p + 2)) :
    fstH (Sx.face y i) = fstH y := by
  unfold fstH
  rw [map_face]
  rfl

theorem fstH_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    fstH (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = fstH y ≫ g := by
  unfold fstH
  rw [map_map, prod.map_fst]
  rfl

theorem snd_map {U U' V : Scheme.{0}} {p : ℕ} (g : U' ⟶ U) (y : Sx (sch.obj U' ⨯ fibQ q N) p V) :
    Sx.map (prod.snd : sch.obj U ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (sch.map g) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y := by
  rw [map_map, prod.map_snd, Category.comp_id]

variable {I₁ I₂ K : Cx R} (μ : Pair I₁ I₂ K) {n : ℤ} (z : Cochain ((chains R).obj (fibQ q N)) I₂ n)

def pval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : Sec (K.X s) V :=
  μ.mul V m (-(p : ℤ) + n) s (by omega) (Sec.res (fstH y) a) (ev z p (-(p : ℤ) + n) rfl V (Sx.map prod.snd y))

theorem pval_res {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    {V' V : Scheme.{0}} (g : V' ⟶ V) (y : Sx (sch.obj U ⨯ fibQ q N) p V) :
    Sec.res g (pval μ z hw a p s hs V y) = pval μ z hw a p s hs V' (y.res g) := by
  unfold pval
  rw [μ.nat, res_res, ev_res, map_sres, fstH_res]

def cval {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) :
    Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) K w :=
  (ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose

theorem cval_ev {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a : Sec (I₁.X m) U) (p : ℕ) (s : ℤ) (hs : -(p : ℤ) + w = s)
    (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p V) : ev (cval μ z hw a) p s hs V y = pval μ z hw a p s hs V y :=
  (ev_exists (pval μ z hw a) (fun p s hs V' V g y => pval_res μ z hw a p s hs g y)).choose_spec p s hs V y

theorem cval_add {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (a b : Sec (I₁.X m) U) :
    cval μ z hw (a + b) = cval μ z hw a + cval μ z hw b := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_add, cval_ev, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (a + b) = Sec.res (fstH y) a + Sec.res (fstH y) b from map_add _ _ _, LinearMap.map_add₂]

theorem cval_smul {U : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (r : ULift.{1} R) (a : Sec (I₁.X m) U) :
    cval μ z hw (r • a) = r • cval μ z hw a := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_smul, cval_ev, cval_ev]
  unfold pval
  rw [show Sec.res (fstH y) (r • a) = r • Sec.res (fstH y) a from map_smul _ _ _, LinearMap.map_smul₂]

theorem cval_nat {U U' : Scheme.{0}} {m w : ℤ} (hw : m + n = w) (g : U' ⟶ U) (a : Sec (I₁.X m) U) :
    cval μ z hw (Sec.res g a) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (cval μ z hw a) (zero_add w) := by
  refine ev_ext _ _ fun p s hs V y => ?_
  rw [ev_pull, cval_ev, cval_ev]
  unfold pval
  rw [fstH_map, snd_map, res_res]

def pmor {m w : ℤ} (hw : m + n = w) : (I₁.X m).obj ⟶ cotPre R q N K w where
  app U := ModuleCat.ofHom
    { toFun := fun a => cval μ z hw (U := U.unop) a
      map_add' := cval_add μ z hw
      map_smul' := cval_smul μ z hw }
  naturality U U' f := by
    ext a : 2
    exact cval_nat μ z hw f.unop a

def smor {m w : ℤ} (hw : m + n = w) : I₁.X m ⟶ (Jcx R q N K).X w :=
  ObjectProperty.homMk (pmor μ z hw ≫ toSheafify Scheme.etaleTopology.{0} (cotPre R q N K w))

def psiC : Cochain I₁ (Jcx R q N K) n := Cochain.mk fun m w hw => smor μ z hw

theorem psiC_v {m w : ℤ} (hw : m + n = w) : (psiC μ z).v m w hw = smor μ z hw := Cochain.mk_v _ _ _ _

theorem Jcx_d (w : ℤ) : (Jcx R q N K).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N K w) := by
  simp [Jcx]

theorem mul_d_congr {V : Scheme.{0}} {m T t1 t2 w : ℤ} (e : t1 = t2) (h1 : m + t1 = w) (h2 : m + t2 = w)
    (A : Sec (I₁.X m) V) (B : Sec (I₂.X T) V) :
    μ.mul V m t1 w h1 A (Sec.map (I₂.d T t1) B) = μ.mul V m t2 w h2 A (Sec.map (I₂.d T t2) B) := by
  subst e
  rfl

theorem cval_δ (hn : Even n) (hz : δ n (n + 1) z = 0) {U : Scheme.{0}} {m w w' : ℤ} (hw : m + n = w)
    (hw' : m + 1 + n = w') (a : Sec (I₁.X m) U) :
    δ w w' (cval μ z hw a) = cval μ z hw' (Sec.map (I₁.d m (m + 1)) a) := by
  have hww : w + 1 = w' := by omega
  refine ev_ext _ _ fun k t ht V y => ?_
  rcases k with _ | k
  · rw [ev_δ_zero hww _ V w t (by simp) ht y, cval_ev, cval_ev]
    unfold pval
    obtain rfl : t = w + 1 := by simp at ht; omega
    rw [μ.leibniz]
    have hz0 : Sec.map (I₂.d (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + n + 1))
        (ev z 0 (-((0 : ℕ) : ℤ) + n) rfl V (Sx.map prod.snd y)) = 0 := by
      rw [← ev_δ_zero (n := n) (m := n + 1) rfl z V _ _ rfl (by omega), hz, ev_zero]
    rw [hz0, map_zero, smul_zero, add_zero, map_res]
  · rw [ev_δ_succ hww _ V k (-((k + 1 : ℕ) : ℤ) + w) t rfl ht y, cval_ev]
    obtain rfl : t = -((k + 1 : ℕ) : ℤ) + w + 1 := by omega
    have e2 : ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ev (cval μ z hw a) k (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega) V (y.face i) =
        ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • μ.mul V m (-(k : ℤ) + n) (-((k + 1 : ℕ) : ℤ) + w + 1) (by omega)
          (Sec.res (fstH y) a) (ev z k (-(k : ℤ) + n) rfl V ((Sx.map prod.snd y).face i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cval_ev]
      unfold pval
      rw [fstH_face, map_face]
    rw [e2, cval_ev]
    unfold pval
    rw [μ.leibniz, mul_d_congr μ (t2 := -(k : ℤ) + n) (by push_cast; omega) _ (by push_cast; omega)]
    have hzS := ev_δ_succ (n := n) (m := n + 1) rfl z V k (-((k + 1 : ℕ) : ℤ) + n) (-(k : ℤ) + n) rfl (by push_cast; omega)
      (Sx.map prod.snd y)
    rw [hz, ev_zero, Int.negOnePow_succ, Int.negOnePow_even n hn, Units.neg_smul, one_smul, eq_comm,
      add_neg_eq_zero] at hzS
    rw [hzS, map_sum, ← map_res]
    have hs : w'.negOnePow = -m.negOnePow := by
      rw [← hw', Int.negOnePow_add, Int.negOnePow_succ, Int.negOnePow_even n hn, mul_one]
    simp only [map_zsmul]
    rw [hs, Units.neg_smul]
    exact add_neg_cancel_right _ _

theorem psiC_δ (hn : Even n) (hz : δ n (n + 1) z = 0) : δ n (n + 1) (psiC μ z) = 0 := by
  refine Cochain.ext _ _ fun p q' hpq => ?_
  obtain ⟨w, rfl⟩ : ∃ w, q' = w + 1 := ⟨q' - 1, by omega⟩
  rw [δ_v n (n + 1) rfl _ p (w + 1) hpq w (p + 1) (by omega) rfl, psiC_v, psiC_v, Jcx_d, Int.negOnePow_succ,
    Int.negOnePow_even n hn, Cochain.zero_v, Units.neg_smul, one_smul, add_neg_eq_zero]
  apply Sheaf.hom_ext
  change pmor μ z _ ≫ toSheafify _ _ ≫ sheafifyMap _ (cotD R q N K w) =
    (I₁.d p (p + 1)).hom ≫ pmor μ z _ ≫ toSheafify _ _
  rw [← toSheafify_naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact cval_δ μ z hn hz _ _ a

end GlobalTheory.EtC.PsiModel

namespace GlobalTheory.EtC.PsiModel

theorem psi_exists : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  intro q N i₁ i₂ i h d z
  subst h
  refine ⟨Cocycle.mk (psiC (twPair q i₁ i₂) z.1) (2 * (d : ℤ) + 1) rfl
    (psiC_δ _ _ (even_two_mul _) (z.δ_eq_zero _)), fun m w hw U a => ⟨cval (twPair q i₁ i₂) z.1 hw a, ?_, fun k s hs V y => ?_⟩⟩
  · change Sec.map ((psiC (twPair q i₁ i₂) z.1).v m w hw) a = _
    rw [psiC_v]
    rfl
  · rw [cval_ev]
    rfl

end GlobalTheory.EtC.PsiModel

end
