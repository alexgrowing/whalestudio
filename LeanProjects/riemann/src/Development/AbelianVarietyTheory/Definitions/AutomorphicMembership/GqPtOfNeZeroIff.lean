import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PrimInIffSubsingleton
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P

def normOf (P : Matrix (Fin n) (Fin (r + 1)) E) : E := -pairM σ J P P (Fin.last r) (Fin.last r)

open scoped Classical in

def nullPt (T T' : E) (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) :=
  if h : ∃ w : Formalism.MainNotions.S.Point E (r + 1), Gq σ T T' (Formalism.MainNotions.S.ptMat w) = 0 then h.choose else onePt E r

open scoped Classical in

def ptOrNull (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Formalism.MainNotions.S.Point E (r + 1) :=
  if ∃ w, LiesAt w Z then ptOfMat Z else nullPt σ T T' r

variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

def mk (c : Col σ J P) (A : Matrix (Fin n) (Fin (r + 1)) E) (h : admitted σ J T' g c.lat P A) : Term σ J T' g P :=
  ⟨c, Quot.mk _ ⟨A, h⟩⟩

variable (t : Term σ J T' g P)

def col : Col σ J P := t.1

def lat : Submodule (𝓞 E) (Fin n → E) := t.col.lat

def fr : Matrix (Fin n) (Fin (r + 1)) E := (Quot.out t.2).1

def Zhat : Matrix (Fin (r + 1)) (Fin (r + 1)) E := pairM σ J t.fr P

def minor (l : ℕ) (hl : l ≤ r + 1) : E := SgAlg.lead t.Zhat l hl

def G : E := Gq σ (normOf σ J P) T' t.Zhat

def GF (F : Type) [Field F] [Algebra F E] : F := Function.invFun (algebraMap F E) t.G

def isId : Prop := ∃ h : admitted σ J T' g t.col.lat P P, t = mk t.col P h

def inS : Prop := Unip P t.fr

def FeqF : Prop := Move σ J t.lat P P t.fr

def sameFlag : Prop := SameFlag P t.fr

def relevant : Prop := Relevant σ J P t.fr

def M : Submodule (𝓞 E) (Fin n → E) := defLat g t.lat P t.fr

abbrev BB : Type := Defect t.M t.lat

def BBne (F : Type) [Field F] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) : Prop := DefectAt F t.M t.lat p

def prim : Prop := PrimIn t.M t.lat

def generic : Prop := t.G ≠ 0 ∧ PrimIn t.M t.lat

def At (w : Formalism.MainNotions.S.Point E (r + 1)) : Prop := LiesAt w t.Zhat

def ptOf : Formalism.MainNotions.S.Point E (r + 1) := ptOrNull σ (normOf σ J P) T' t.Zhat

def Carries {P₀ : Matrix (Fin n) (Fin (r + 1)) E} (c' : Col σ J P₀) (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J γ ∧ latMap γ c'.lat = t.lat ∧ Move σ J t.lat P (γ * P₀) t.fr

def Rep (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  Transp σ J P t.lat t.fr Λ A

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}

omit [NumberField E] in

theorem normOf_eq (hP : IsFrame σ J T P) : normOf σ J P = T := by
  rw [normOf, hP.2]; simp [TF]

omit [NumberField E] in

theorem ptEntry_replicate (ζ : E) : ∀ (m i j : ℕ), Formalism.MainNotions.S.ptEntry (List.replicate m ((1 : E), 1) ++ [(ζ, 1)]) i j =
    if i = j then (if i < m then 1 else if i = m then ζ else 0) else 0
  | 0, i, j => by
    simp only [List.replicate_zero, List.nil_append, Formalism.MainNotions.S.ptEntry]
    split_ifs <;> first | rfl | omega
  | m + 1, i, j => by
    rw [List.replicate_succ, List.cons_append, Formalism.MainNotions.S.ptEntry, ptEntry_replicate ζ m]
    split_ifs <;> first | rfl | omega

omit [NumberField E] in

theorem Gq_nullPt {ζ : E} (hζ : ζ ≠ 0) (h : ζ * σ ζ = T * T') :
    Gq σ T T' (Formalism.MainNotions.S.ptMat (nullPt σ T T' r)) = 0 := by
  have k : ∃ w : Formalism.MainNotions.S.Point E (r + 1), Gq σ T T' (Formalism.MainNotions.S.ptMat w) = 0 := by
    let w : Formalism.MainNotions.S.Point E (r + 1) := ⟨List.replicate r ((1 : E), 1) ++ [(ζ, 1)], fun b hb => by
      rcases List.mem_append.1 hb with hb | hb
      · rw [List.eq_of_mem_replicate hb]; simp
      · rw [List.mem_singleton.1 hb]; simpa using hζ, by simp⟩
    have e : Formalism.MainNotions.S.ptMat w = Matrix.diagonal fun a => if a = Fin.last r then ζ else 1 := by
      ext a b
      have := a.2
      rw [Formalism.MainNotions.S.ptMat, ptEntry_replicate, Matrix.diagonal_apply]
      simp only [Fin.ext_iff, Fin.val_last]
      split_ifs <;> first | rfl | omega
    have h1 : (Formalism.MainNotions.S.ptMat w).det = ζ := by
      simp [e, Fin.prod_univ_castSucc, (Fin.castSucc_lt_last _).ne]
    have h2 : SgAlg.lead (Formalism.MainNotions.S.ptMat w) r (Nat.le_succ r) = 1 := by
      rw [SgAlg.lead, e, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
      exact Finset.prod_eq_one fun i _ => if_neg (Fin.castSucc_lt_last i).ne
    exact ⟨w, by rw [Gq, h1, h2, h, map_one]; ring⟩
  rw [nullPt, dif_pos k]; exact k.choose_spec

omit [NumberField E] in

theorem Gq_mul_eps (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Gq σ T T' (Z * eps E r) = Gq σ T T' Z := by
  have k (l : ℕ) (hl : l ≤ r + 1) : SgAlg.lead (Z * eps E r) l hl * σ (SgAlg.lead (Z * eps E r) l hl) =
      SgAlg.lead Z l hl * σ (SgAlg.lead Z l hl) := by
    have e : (Z * eps E r).submatrix (Fin.castLE hl) (Fin.castLE hl) = Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal fun b : Fin l => (-1 : E) ^ (r - (b : ℕ)) := by
      ext a b; simp [eps]
    have s : (∏ b : Fin l, (-1 : E) ^ (r - (b : ℕ))) * σ (∏ b : Fin l, (-1 : E) ^ (r - (b : ℕ))) = 1 := by
      simp [← Finset.prod_mul_distrib, ← mul_pow]
    rw [SgAlg.lead, e, Matrix.det_mul, Matrix.det_diagonal, map_mul, mul_mul_mul_comm, s, mul_one, SgAlg.lead]
  have k1 : (Z * eps E r).det * σ (Z * eps E r).det = Z.det * σ Z.det := k (r + 1) le_rfl
  rw [Gq, Gq, k, k1]

omit [NumberField E] in

theorem LiesAt.Gq_eq {w : Formalism.MainNotions.S.Point E (r + 1)} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : LiesAt w Z)
    (T T' : E) : Gq σ T T' (Formalism.MainNotions.S.ptMat w) = Gq σ T T' Z := by
  obtain ⟨l, u, hl, hu, e⟩ := h
  rw [← Gq_mul_eps T T' Z, e, Gq_mul T T' hl hu]

theorem Col.lat_mem (c : Col σ J P) : c.lat ∈ FrameLats σ J P := (Quot.out c).2

theorem Col.existsUnique (hJ : IsUnit J.det) (h : Λ ∈ FrameLats σ J P) :
    ∃! c : Col σ J P, ∃ s, InS σ J P s ∧ latMap s Λ = c.lat := by
  have hre : Equivalence fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1 :=
    ⟨fun _ => ⟨1, inS_one, latMap_one _⟩, fun ⟨s, hs, e⟩ => ⟨s⁻¹, inS_inv hJ hs, by
      rw [← e, ← latMap_mul, Matrix.nonsing_inv_mul s (isUnit_det_of_isUn hJ hs.1), latMap_one]⟩,
      fun ⟨s, hs, e⟩ ⟨t, ht, f⟩ => ⟨t * s, inS_mul ht hs, by rw [latMap_mul, e, f]⟩⟩
  refine ⟨Quot.mk _ ⟨Λ, h⟩,
    hre.eqvGen_iff.1 (Quot.eq.1 (Quot.out_eq (Quot.mk _ (⟨Λ, h⟩ : FrameLats σ J P))).symm), fun c hc => ?_⟩
  exact (Quot.out_eq c).symm.trans (Quot.sound (a := (⟨Λ, h⟩ : FrameLats σ J P)) hc).symm

namespace Term

variable (t : Term σ J T' g P)

theorem lat_mem : t.lat ∈ FrameLats σ J P := t.col.lat_mem

theorem adm : admitted σ J T' g t.lat P t.fr := (Quot.out t.2).2

theorem mk_fr : mk t.col t.fr t.adm = t := by
  obtain ⟨c, q⟩ := t
  exact congrArg (Sigma.mk c) (Quot.out_eq q)

theorem mk_eq_mk (hJ : IsUnit J.det) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) (hB : admitted σ J T' g c.lat P B) :
    mk c A hA = mk c B hB ↔ Move σ J c.lat P A B := by
  have hre : Equivalence fun A B : {A // admitted σ J T' g c.lat P A} => Move σ J c.lat P A.1 B.1 :=
    (move_equivalence hJ).comap Subtype.val
  exact ⟨fun h => hre.eqvGen_iff.1 (Quot.eq.1 (eq_of_heq (Sigma.mk.inj h).2)),
    fun h => congrArg (Sigma.mk c) (Quot.sound h)⟩

theorem move_fr_mk (hJ : IsUnit J.det) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) :
    Move σ J c.lat P (mk c A hA).fr A :=
  (mk_eq_mk hJ c (mk c A hA).adm hA).1 (mk c A hA).mk_fr

theorem rep_mk (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (c : Col σ J P) (hA : admitted σ J T' g c.lat P A) :
    (mk c A hA).Rep c.lat A := (move_fr_mk hJ c hA).transp hP

theorem rep_self : t.Rep t.lat t.fr := Transp.refl

theorem exists_rep (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (h : Λ ∈ FrameLats σ J P)
    (hA : admitted σ J T' g Λ P A) : ∃ t : Term σ J T' g P, t.Rep Λ A := by
  obtain ⟨c, ⟨s, hs, e⟩, -⟩ := Col.existsUnique hJ h
  have k : Transp σ J P Λ A c.lat (s * A) := ⟨s, hs, e, 1, one_mem_UO, (Matrix.mul_one _).symm⟩
  exact ⟨_, (rep_mk hJ hP c (k.adm hJ hP.1 h.2 c.lat_mem.2 hA)).trans (k.symm hJ)⟩

variable {t}

theorem Rep.minor_eq (h : t.Rep Λ A) (l : ℕ) (hl : l ≤ r + 1) :
    t.minor l hl = SgAlg.lead (pairM σ J A P) l hl := (Transp.lead_eq h l hl).symm

theorem Rep.G_eq (h : t.Rep Λ A) (hP : IsFrame σ J T P) : t.G = Gq σ T T' (pairM σ J A P) := by
  rw [Term.G, normOf_eq hP]; exact (Transp.Gq_eq h T T').symm

theorem Rep.relevant_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) : t.relevant ↔ Relevant σ J P A :=
  (Transp.relevant_iff hJ h).symm

theorem Rep.inS_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) : t.inS ↔ Unip P A := (Transp.unip_iff hJ h).symm

theorem Rep.sameFlag_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) : t.sameFlag ↔ SameFlag P A :=
  (Transp.sameFlag_iff hJ h).symm

theorem Rep.at_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) (w : Formalism.MainNotions.S.Point E (r + 1)) :
    t.At w ↔ LiesAt w (pairM σ J A P) := (Transp.liesAt_iff hJ h w).symm

theorem Rep.ptOf_eq (h : t.Rep Λ A) (hJ : IsUnit J.det) :
    t.ptOf = ptOrNull σ (normOf σ J P) T' (pairM σ J A P) := by
  rw [Term.ptOf, ptOrNull, ptOrNull, ptOfMat_congr (h.at_iff hJ)]
  classical
  exact if_congr (exists_congr (h.at_iff hJ)) rfl rfl

theorem Rep.BBne_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (hΛ : Λ ∈ FrameLats σ J P)
    (F : Type) [Field F] [Algebra F E] (p : HeightOneSpectrum (𝓞 F)) :
    t.BBne F p ↔ DefectAt F (defLat g Λ P A) Λ p := by
  obtain ⟨s, hs, e1, e2⟩ := Transp.defLat_eq (g := g) hJ hP.1 t.lat_mem.2 hΛ.2 h
  rw [← e2]
  conv_rhs => enter [3]; rw [← e1]
  exact (defectAt_latMap F hs p).symm

theorem Rep.prim_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (hΛ : Λ ∈ FrameLats σ J P) :
    t.prim ↔ PrimIn (defLat g Λ P A) Λ := by
  obtain ⟨s, hs, e1, e2⟩ := Transp.defLat_eq (g := g) hJ hP.1 t.lat_mem.2 hΛ.2 h
  rw [← e2]
  conv_rhs => enter [2]; rw [← e1]
  exact (primIn_latMap hs).symm

theorem Rep.generic_iff (h : t.Rep Λ A) (hJ : IsUnit J.det) (hP : IsFrame σ J T P) (hΛ : Λ ∈ FrameLats σ J P) :
    t.generic ↔ Gq σ T T' (pairM σ J A P) ≠ 0 ∧ PrimIn (defLat g Λ P A) Λ := by
  obtain ⟨s, hs, e1, e2⟩ := Transp.defLat_eq (g := g) hJ hP.1 t.lat_mem.2 hΛ.2 h
  rw [← e2, ← h.G_eq hP]
  conv_rhs => enter [2, 2]; rw [← e1]
  exact and_congr_right fun _ => (primIn_latMap hs).symm

variable (t)

theorem G_eq_minor (hP : IsFrame σ J T P) :
    t.G = t.minor (r + 1) le_rfl * σ (t.minor (r + 1) le_rfl) -
      T * T' * (t.minor r (Nat.le_succ r) * σ (t.minor r (Nat.le_succ r))) := by
  rw [Term.G, normOf_eq hP]; rfl

theorem algebraMap_GF (F : Type) [Field F] [Algebra F E] (hσ : ∀ x, σ (σ x) = x)
    (hF : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (hP : IsFrame σ J T P) (hT : σ T = T) (hT' : σ T' = T') :
    algebraMap F E (t.GF F) = t.G :=
  Function.invFun_eq (hF _ (map_Gq hσ (by rwa [normOf_eq hP]) hT'))

theorem M_eq (hg : g ≠ 0) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hu : u ∈ UO E r)
    (h : Cong g t.lat (P * u) t.fr) : t.M = pairLat g (P * u) t.fr :=
  defLat_eq_pairLat hg t.lat_mem.2 hu h

theorem M_le : t.M ≤ t.lat := inf_le_left

theorem prim_iff_BB : t.prim ↔ Subsingleton t.BB := primIn_iff_subsingleton t.M_le

theorem prim_iff_BBne (F : Type) [Field F] [NumberField F] [Algebra F E] : t.prim ↔ ∀ p, ¬ t.BBne F p :=
  primIn_iff_defectAt F t.M_le

theorem generic_iff : t.generic ↔ t.G ≠ 0 ∧ t.prim := Iff.rfl

theorem generic_iff_BB : t.generic ↔ t.G ≠ 0 ∧ Subsingleton t.BB :=
  and_congr_right fun _ => primIn_iff_subsingleton t.M_le

theorem generic_iff_BBne (F : Type) [Field F] [NumberField F] [Algebra F E] :
    t.generic ↔ t.G ≠ 0 ∧ ∀ p, ¬ t.BBne F p :=
  and_congr_right fun _ => primIn_iff_defectAt F t.M_le

theorem generic.mem_genConf {t : Term σ J T' g P} (h : t.generic) (hg : g ≠ 0) (hP : IsFrame σ J T P) :
    ∃ u ∈ UO E r, ((t.lat, P * u, t.fr) : Tri E n r) ∈ GenConf σ J T T' g (cT σ u * t.Zhat) := by
  obtain ⟨u, hu, k⟩ := t.adm.2
  refine ⟨u, hu, t.lat_mem.1, ⟨isFrame_mul hP hu.1, t.adm.1.1, ?_⟩, t.M_eq hg hu k ▸ h.2⟩
  simpa [Term.Zhat] using pairM_mul (σ := σ) (J := J) (P := P) (P' := t.fr) 1 u

theorem at_ptOf (h : ∃ w, t.At w) : t.At t.ptOf := by
  rw [Term.ptOf, ptOrNull, if_pos (show ∃ w, LiesAt w t.Zhat from h)]; exact liesAt_ptOfMat h

theorem At.Gq_eq {t : Term σ J T' g P} {w : Formalism.MainNotions.S.Point E (r + 1)} (h : t.At w) (hP : IsFrame σ J T P) :
    Gq σ T T' (Formalism.MainNotions.S.ptMat w) = t.G := by
  rw [Term.G, normOf_eq hP]; exact LiesAt.Gq_eq h T T'

theorem Gq_ptOf_of_not_at (hP : IsFrame σ J T P) {ζ : E} (hζ : ζ ≠ 0) (h : ζ * σ ζ = T * T')
    (k : ¬ ∃ w, t.At w) : Gq σ T T' (Formalism.MainNotions.S.ptMat t.ptOf) = 0 := by
  rw [Term.ptOf, ptOrNull, if_neg (show ¬ ∃ w, LiesAt w t.Zhat from k), normOf_eq hP]; exact Gq_nullPt hζ h

theorem Gq_ptOf_ne_zero_iff (hP : IsFrame σ J T P) {ζ : E} (hζ : ζ ≠ 0) (h : ζ * σ ζ = T * T') :
    Gq σ T T' (Formalism.MainNotions.S.ptMat t.ptOf) ≠ 0 ↔ t.G ≠ 0 ∧ t.At t.ptOf := by
  refine ⟨fun k => ?_, fun k => by rw [k.2.Gq_eq hP]; exact k.1⟩
  have a := t.at_ptOf (by_contra fun a => k (t.Gq_ptOf_of_not_at hP hζ h a))
  exact ⟨a.Gq_eq hP ▸ k, a⟩

theorem isId_iff_FeqF (hJ : IsUnit J.det) (hP : IsFrame σ J T P) : t.isId ↔ t.FeqF := by
  constructor
  · rintro ⟨h, e⟩
    exact (move_equivalence hJ).symm ((mk_eq_mk hJ t.col t.adm h).1 (t.mk_fr.trans e))
  · intro h
    have k : Unip P t.fr := (Transp.unip_iff hJ (Move.transp hP h)).2 ⟨1, up_one, by simp⟩
    obtain rfl := k.norm_eq hP t.adm.1.1
    exact ⟨tower_admissible_self ⟨hP, t.lat_mem.2⟩,
      t.mk_fr.symm.trans ((mk_eq_mk hJ t.col t.adm _).2 ((move_equivalence hJ).symm h))⟩

theorem inS_iff_FeqF (hJ : IsUnit J.det) (hP : IsFrame σ J T P) : t.inS ↔ t.FeqF := by
  refine ⟨fun h => ?_, fun h => (Transp.unip_iff hJ (Move.transp hP h)).2 ⟨1, up_one, by simp⟩⟩
  obtain ⟨a, ha, e⟩ := Unip.exists_UO h ⟨hP, t.lat_mem.2⟩ t.adm.1.2.1
  exact ⟨1, ⟨inN_one, latMap_one _⟩, a, ha, by rwa [Matrix.one_mul]⟩

theorem inS_iff_of_carries (hJ : IsUnit J.det) (hP : IsFrame σ J T P) {c' : Col σ J P}
    {γ : Matrix (Fin n) (Fin n) E} (h : t.Carries c' γ) : t.inS ↔ InS σ J P γ :=
  (Transp.unip_iff hJ (Move.transp hP h.2.2)).trans ⟨fun k => inS_iff.2 ⟨h.1, k⟩, fun k => (inS_iff.1 k).2⟩

theorem inS.props {t : Term σ J T' g P} (h : t.inS) (hP : IsFrame σ J T P) (hT : σ T = T) :
    t.sameFlag ∧ t.relevant ∧ t.G = 0 ∧ T' = T := by
  obtain rfl := Unip.norm_eq h hP t.adm.1.1
  obtain ⟨a, ha, e⟩ := h
  refine ⟨⟨a, up_tri ha, by simp [up_det ha], e⟩, ?_, ?_, rfl⟩
  · simpa [Term.relevant, e] using (relevant_self (σ := σ) (J := J) hP.1).mul up_one ha
  · have k := pairM_mul (σ := σ) (J := J) (P := P) (P' := P) a 1
    rw [Matrix.mul_one, ← e, hP.2] at k
    rw [Term.G, normOf_eq hP, Term.Zhat, k, Gq_mul _ _ (lo_cT σ up_one) ha, Gq_TF hT]

theorem inS.prim {t : Term σ J T' g P} (h : t.inS) (hP : IsFrame σ J T P) : t.prim := by
  obtain ⟨a, ha, e⟩ := Unip.exists_UO h ⟨hP, t.lat_mem.2⟩ t.adm.1.2.1
  refine ⟨t.M_le, fun v hv k => (mem_defLat v).2 ⟨hv, Submodule.mem_sup_left ?_⟩⟩
  rw [Nat.cast_smul_eq_nsmul]
  by_cases hg : g = 0
  · simp [hg]
  refine nsmul_mem (t.lat_mem.2.2 v hv (Submodule.span_le.2 (fun x hx => ?_) k)) g
  have := ((mem_defLat x).1 hx).2
  rw [e, frameLat_mul ha, sup_idem] at this
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hg)).1 (Submodule.subset_span this)

theorem existsUnique_isId (hP : IsFrame σ J T P) (c : Col σ J P) :
    ∃! t : Term σ J T g P, t.col = c ∧ t.isId :=
  ⟨mk c P (tower_admissible_self ⟨hP, c.lat_mem.2⟩), ⟨rfl, _, rfl⟩, fun t ⟨e, h, k⟩ => by subst e; exact k⟩

theorem exists_generic (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermU σ J) (hg : g ≠ 0)
    {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : ((Λ, P, A) : Tri E n r) ∈ GenConf σ J T T' g Z)
    (hG : Gq σ T T' Z ≠ 0) : ∃ t : Term σ J T' g P, t.Rep Λ A ∧ t.generic ∧ t.G = Gq σ T T' Z := by
  obtain ⟨h1, ⟨h2, h3, h4⟩, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h4
  obtain ⟨k1, k2⟩ := Iota.primIn_frameLat (Nat.cast_ne_zero.2 hg) h5
    (Iota.indep_of_Gq_ne_zero hσ hJ.1 ⟨h2, h3, rfl⟩ hG)
  have hc : Cong g Λ (P * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) A := by
    rw [Matrix.mul_one]; exact le_sup_right.trans h5.1
  obtain ⟨t, ht⟩ := exists_rep hJ.2 h2 ⟨h1, k1⟩ ⟨⟨h3, k2⟩, 1, one_mem_UO, hc⟩
  refine ⟨t, ht, (ht.generic_iff hJ.2 h2 ⟨h1, k1⟩).2 ⟨hG, ?_⟩, ht.G_eq h2⟩
  rwa [defLat_eq_pairLat hg k1 one_mem_UO hc, Matrix.mul_one]

end Term

end Basic

section Examples

variable {E : Type} [Field E] [NumberField E]

theorem exists_term_plane (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {g : ℕ} (hg : g ≠ 0) :
    ∃ t : Term (r := 0) σ !![1, 0; 0, -1] (1 + 2 * g) g !![0; 1], t.generic ∧ t.G = (g : E) ^ 2 ∧ ¬ t.inS := by
  have hG : Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] ≠ 0 := by
    rw [Inhab.gq_zero]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hg)
  obtain ⟨t, -, h1, h2⟩ := Term.exists_generic hσ (Inhab.inhabitants σ hg).1.1 hg (Inhab.mem_genConf_zero σ hg) hG
  exact ⟨t, h1, h2.trans (Inhab.gq_zero σ g),
    fun h => h1.1 (h.props (Inhab.mem_genConf_zero σ hg).2.1.1 (map_one σ)).2.2.1⟩

theorem exists_term_split (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) {g : ℕ} (hg : g ≠ 0) :
    (∃ t : Term σ (Inhab.splitJ E) (1 + 2 * g) g (Inhab.splitP E), t.generic) ∧
      ∃ t : Term σ (Inhab.splitJ E) 1 g (Inhab.splitP E), t.isId := by
  obtain ⟨a, b, ha, hab⟩ := Inhab.exists_different_pair E
  have h := Inhab.mem_genConf_one σ hσ hg hab
  obtain ⟨t, -, h1, -⟩ := Term.exists_generic hσ (Inhab.isHermU_splitJ σ) hg h (by
    rw [Inhab.gq_one σ hσ]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hg))
      (Inhab.norm_add_norm_ne_zero σ τ hτ (by simpa using ha) _)))
  obtain ⟨t', h2, -⟩ := Term.existsUnique_isId (g := g) h.2.1.1 t.col
  exact ⟨⟨t, h1⟩, t', h2.2⟩

example : LiesAt (onePt E 1) !![0, 1; -1, 0] :=
  ⟨1, 1, fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne, fun h => h ▸ Matrix.one_apply_eq _⟩, up_one, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [eps, onePt, Formalism.MainNotions.S.ptMat, Formalism.MainNotions.S.ptEntry]⟩

example (σ : E →+* E) :
    ¬ Relevant (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1] !![1, 0; 0, 0; 0, 1] !![-1, 0; 0, 0; 0, 1] := by
  intro h
  have k (c : E) (hc : c * c = 1) (hs : σ c = c) : LieN (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1]
      !![c, 0; 0, 0; 0, 1] !![0, 0, 1; 0, 0, 0; 0, 1, 0] !![0, c; 0, 0] := by
    refine ⟨?_, fun i j hij => ?_, ?_, fun x hx => ⟨![c * x 2], ?_⟩⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [cT, Matrix.mul_apply, Fin.sum_univ_three]
    · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hc]
    · have h1 : x 1 = 0 := by
        have := (mem_perpX_iff_form _ _).1 hx 0
        have hc0 : c ≠ 0 := fun e => by simp [e] at hc
        simpa [form, dotProduct, Matrix.mulVec, Fin.sum_univ_three, hs, hc0] using this
      ext i
      fin_cases i <;> simp [eOf, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, ← mul_assoc, hc]
  have := h _ _ _ (k 1 (by simp) (by simp)) (k (-1) (by simp) (by simp))
  simp [simpleSum] at this

end Examples

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coMat (V : HSpace E) {a : Type} (x : a → V.V) : Matrix (Fin V.rank) a E :=
  Matrix.of fun i b => V.frame.repr (x b) i

theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

theorem pairM_coMat (V : HSpace E) {a b : Type} (x : a → V.V) (y : b → V.V) (i : a) (j : b) :
    pairM (starRingEnd E) V.gram (coMat V y) (coMat V x) i j = V.hD (y j) (x i) := by
  rw [HSpace.hD, hT_eq_sum]; rfl

theorem isHermU_gram (V : HSpace E) : IsHermU (starRingEnd E) V.gram := by
  refine ⟨Matrix.ext fun i j => V.herm.eq _ _, isUnit_iff_ne_zero.2 fun h => ?_⟩
  obtain ⟨v, hv, e⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  have : V.frame.equivFun.symm (star v) = 0 := V.nondeg.1 _ fun y => by
    rw [hT_eq_sum]
    refine Finset.sum_eq_zero fun j _ => mul_eq_zero_of_left ?_ _
    simp only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, Pi.star_apply, star_star]
    exact congrFun e j
  exact hv (star_eq_zero.1 ((map_eq_zero_iff _ V.frame.equivFun.symm.injective).1 this))

def spFrame (S : Spaces R F E) (c : E) : Matrix (Fin (S.Y 0).rank) (Fin (R.rS + 1)) E :=
  coMat (S.Y 0) (Fin.snoc (α := fun _ => (S.Y 0).V) S.hypE (c • S.zm))

theorem isFrame_spFrame (S : Spaces R F E) {c : E} (hc : c ≠ 0) :
    IsFrame (starRingEnd E) (S.Y 0).gram (c * star c * S.T) (spFrame S c) := by
  have hT : (S.T : E) ≠ 0 := Nat.cast_ne_zero.2 S.T_prime.ne_zero
  have sw {x y : (S.Y 0).V} {a : E} (h : (S.Y 0).hT x y = a) : (S.Y 0).hT y x = star a := by
    rw [← h]; exact ((S.Y 0).herm.eq x y).symm
  refine ⟨⟨cT (starRingEnd E) (coMat (S.Y 0) (Fin.snoc (α := fun _ => (S.Y 0).V) S.hypF
    ((-(star c * S.T)⁻¹) • S.zm))) * (S.Y 0).gram, ?_⟩, ?_⟩
  · ext a b
    refine (pairM_coMat _ _ _ a b).trans ?_
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · simp [HSpace.hD, S.zm_norm, starRingEnd_apply]
      field_simp
    · simp [HSpace.hD, (S.hyp_orthz _).1, (Fin.castSucc_lt_last _).ne']
    · simp [HSpace.hD, sw (S.hyp_orthz _).2, (Fin.castSucc_lt_last _).ne]
    · simp [HSpace.hD, sw (S.hyp_ef _ _), Matrix.one_apply, eq_comm, apply_ite star]
  · ext a b
    refine (pairM_coMat _ _ _ a b).trans ?_
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · simp [HSpace.hD, S.zm_norm, TF, starRingEnd_apply]
      ring
    · simp [HSpace.hD, (S.hyp_orthz _).1, TF, (Fin.castSucc_lt_last _).ne']
    · simp [HSpace.hD, sw (S.hyp_orthz _).1, TF, (Fin.castSucc_lt_last _).ne]
    · simp [HSpace.hD, S.hyp_ee, TF, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne]

end Spaces

section Record

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def recFrame (u : D.what₂.Word) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.R.rS + 1)) D.host.E :=
  spFrame D.sp (D.cOf u)⁻¹

abbrev RecCol (u : D.what₂.Word) : Type := Col (starRingEnd D.host.E) (D.sp.Y 0).gram (recFrame D u)

abbrev RecTerm (u u' : D.what₂.Word) : Type :=
  Term (starRingEnd D.host.E) (D.sp.Y 0).gram (((D.mem u').A.T : ℕ) : D.host.E) (D.host.g 0 * D.host.g 1)
    (recFrame D u)

theorem recFrame_eq (u : D.what₂.Word) :
    recFrame D u = coMat (D.sp.Y 0) (Fin.snoc (α := fun _ => (D.sp.Y 0).V) D.sp.hypE (D.zmOf u)) := rfl

theorem isFrame_recFrame (u : D.what₂.Word) :
    IsFrame (starRingEnd D.host.E) (D.sp.Y 0).gram (((D.mem u).A.T : ℕ) : D.host.E) (recFrame D u) := by
  have h := isFrame_spFrame D.sp (inv_ne_zero (D.cOf_ne u))
  have hc := D.cOf_ne u
  have hs : star (D.cOf u) ≠ 0 := star_ne_zero.2 hc
  have e : D.cOf u * star (D.cOf u) * ((D.mem u).A.T : D.host.E) = ((D.mem D.u₀).A.T : D.host.E) := by
    rw [bridge_star_holds D.R D.host]; exact D.cOf_eq u
  rwa [D.sp_T, ← e, star_inv₀, show (D.cOf u)⁻¹ * (star (D.cOf u))⁻¹ *
    (D.cOf u * star (D.cOf u) * ((D.mem u).A.T : D.host.E)) = ((D.mem u).A.T : D.host.E) by field_simp] at h

theorem level_ne_zero : D.host.g 0 * D.host.g 1 ≠ 0 :=
  mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

variable {D} {u u' : D.what₂.Word}

theorem RecTerm.algebraMap_GF (t : RecTerm D u u') :
    algebraMap D.host.F D.host.E (t.GF D.host.F) =
      t.minor (D.R.rS + 1) le_rfl * star (t.minor (D.R.rS + 1) le_rfl) -
        ((D.mem u).A.T : D.host.E) * ((D.mem u').A.T : D.host.E) *
          (t.minor D.R.rS (Nat.le_succ _) * star (t.minor D.R.rS (Nat.le_succ _))) :=
  (Term.algebraMap_GF t D.host.F star_star (fun x => (D.sp.cm.fixed x).1) (isFrame_recFrame D u) (map_natCast _ _)
    (map_natCast _ _)).trans (t.G_eq_minor (isFrame_recFrame D u))

theorem RecTerm.GF_eq_zero_iff (t : RecTerm D u u') : t.GF D.host.F = 0 ↔ t.G = 0 := by
  rw [← Term.algebraMap_GF t D.host.F star_star (fun x => (D.sp.cm.fixed x).1) (isFrame_recFrame D u)
    (map_natCast _ _) (map_natCast _ _), map_eq_zero]

theorem RecTerm.isId_props (t : RecTerm D u u') :
    (t.isId ↔ t.FeqF) ∧ (t.inS ↔ t.FeqF) ∧ (t.isId → t.relevant ∧ t.GF D.host.F = 0) := by
  have hJ := (isHermU_gram (D.sp.Y 0)).2
  have h1 := t.isId_iff_FeqF hJ (isFrame_recFrame D u)
  have h2 := t.inS_iff_FeqF hJ (isFrame_recFrame D u)
  refine ⟨h1, h2, fun h => ?_⟩
  have := (h2.2 (h1.1 h)).props (isFrame_recFrame D u) (map_natCast _ _)
  exact ⟨this.2.1, t.GF_eq_zero_iff.2 this.2.2.1⟩

theorem exists_norm_eq (u u' : D.what₂.Word) : ∃ ζ : D.host.E, ζ ≠ 0 ∧
    ζ * starRingEnd D.host.E ζ = ((D.mem u).A.T : D.host.E) * ((D.mem u').A.T : D.host.E) := by
  have k (u : D.what₂.Word) : ∃ π : D.host.E, π ≠ 0 ∧ π * star π = ((D.mem u).A.T : D.host.E) := by
    obtain ⟨π, -, h, -⟩ := D.T_norm u
    refine ⟨π, fun e => ?_, by rw [bridge_star_holds D.R D.host]; exact h⟩
    have h2 := D.cOf_eq u
    rw [← h, e, zero_mul, mul_zero, ← D.sp_T] at h2
    exact D.sp.T_prime.ne_zero (Nat.cast_eq_zero.1 h2.symm)
  obtain ⟨a, ha, e⟩ := k u
  obtain ⟨b, hb, f⟩ := k u'
  exact ⟨a * b, mul_ne_zero ha hb, by rw [← e, ← f, starRingEnd_apply, star_mul]; ring⟩

theorem RecTerm.Gq_ptOf_ne_zero_iff (t : RecTerm D u u') :
    Gq (starRingEnd D.host.E) ((D.mem u).A.T : D.host.E) ((D.mem u').A.T : D.host.E)
      (Formalism.MainNotions.S.ptMat t.ptOf) ≠ 0 ↔ t.G ≠ 0 ∧ t.At t.ptOf := by
  obtain ⟨ζ, h1, h2⟩ := exists_norm_eq u u'
  exact Term.Gq_ptOf_ne_zero_iff t (isFrame_recFrame D u) h1 h2

theorem RecTerm.isId_prim (t : RecTerm D u u') (h : t.isId) : t.prim ∧
    Gq (starRingEnd D.host.E) ((D.mem u).A.T : D.host.E) ((D.mem u').A.T : D.host.E)
      (Formalism.MainNotions.S.ptMat t.ptOf) = 0 :=
  ⟨(t.isId_props.2.1.2 (t.isId_props.1.1 h)).prim (isFrame_recFrame D u), by_contra fun k =>
    (t.Gq_ptOf_ne_zero_iff.1 k).1 (t.GF_eq_zero_iff.1 (t.isId_props.2.2 h).2)⟩

end Record

end GlobalTheory.IntTerm
