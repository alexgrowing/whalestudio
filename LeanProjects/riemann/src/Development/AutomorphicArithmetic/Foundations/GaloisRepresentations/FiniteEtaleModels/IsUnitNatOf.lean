import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem isUnit_nat_of {E : Type} [Field E] [CharZero E] {V : Scheme.{0}} (s : V ⟶ Sp E) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
  have hE : IsUnit ((n : E)) := (Nat.cast_ne_zero.mpr hn).isUnit
  have h1 : IsUnit ((n : Γ(Sp E, ⊤))) := by
    have := hE.map (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
    simpa using this
  have := h1.map s.appTop.hom
  simpa using this

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'}

private theorem qmap_cast {N₁ N c : ℕ} {V Y : Scheme.{0}} {s : V ⟶ Sp R'} {t : Y ⟶ Sp R} {a : GObj gb N₁ s} {u : Obj b N t}
    {f f' : V ⟶ Y} (h : f = f') (n : QMap a u f c) : ∃ n' : QMap a u f' c, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

private theorem rigid_of (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q) {S₁ S₂ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {f f' : S₁ ⟶ S₂}
    (m : ObjMap o₁ o₂ f) (m' : ObjMap o₁ o₂ f') (h : f = f') : m.φ = m'.φ := by
  subst h
  exact (hO q D R b N hN hNq S₁ S₂ S₂ s₁ s₂ s₂ o₁ o₂ o₂ f (𝟙 _)).1 m m'

private theorem read_tj {N : ℕ} {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c) {V : Scheme.{0}}
    (x : V ⟶ M.X) (s₀ : V ⟶ Sp R) (hx : x ≫ M.s = s₀) (o₁ o₂ : Obj b N s₀) (m : ObjMap o₁ M.univ x) (ψ₀ : o₁.A ⟶ o₂.A)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (_ : y ≫ Tj.s = x) (m₀ : ObjMap o₁ Tj.o y) (m₁ : ObjMap o₂ Tj.o' y),
      m₀.φ ≫ Tj.ψ.left = ψ₀.left ≫ m₁.φ := by
  subst hx
  obtain ⟨y, ⟨hy, m₀, m₁, h⟩, -⟩ := Tj.univ V x o₁ o₂ m ψ₀ hu hi ht
  exact ⟨y, hy, m₀, m₁, h⟩

private theorem read_core (hQ : QComp) (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N N₁ N₂ c₁ c₂ : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c)
    {V Y₁ Y₂ : Scheme.{0}} {s : V ⟶ Sp R'} {s₀ : V ⟶ Sp R} {t₁ : Y₁ ⟶ Sp R} {t₂ : Y₂ ⟶ Sp R}
    {a : GObj gb N₁ s} {a' : GObj gb N₂ s} {o₁ o₂ : Obj b N s₀} {u₁ : Obj b N t₁} {u₂ : Obj b N t₂}
    (n₁ : QMap a o₁ (𝟙 V) c₁) (n₂ : QMap a' o₂ (𝟙 V) c₂) {j₁ : V ⟶ Y₁} {j₂ : V ⟶ Y₂}
    (k₁ : QMap a u₁ j₁ c₁) (k₂ : QMap a' u₂ j₂ c₂) {f : Y₁ ⟶ M.X} {π : Y₂ ⟶ M.X}
    (mf : ObjMap u₁ M.univ f) (mπ : ObjMap u₂ M.univ π)
    (hb₁ : (j₁ ≫ f) ≫ M.s = s₀) (hb₂ : (j₂ ≫ π) ≫ M.s = s₀)
    (ψ' : a.A.left ⟶ a'.A.left) (ψ₀ : o₁.A ⟶ o₂.A) (hψ : n₁.φ ≫ ψ₀.left = ψ' ≫ n₂.φ)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (fa : a.A.left ⟶ Tj.o.A.left) (fb : a'.A.left ⟶ Tj.o'.A.left),
      y ≫ Tj.s = j₁ ≫ f ∧ y ≫ Tj.t = j₂ ≫ π ∧ IsGrpPullback a.A Tj.o.A y fa ∧ IsGrpPullback a'.A Tj.o'.A y fb ∧
      fa ≫ Tj.ψ.left = ψ' ≫ fb ∧ fa ≫ Tj.ms.φ = k₁.φ ≫ mf.φ ∧ fb ≫ Tj.mt.φ = k₂.φ ≫ mπ.φ := by
  obtain ⟨k₁', hk₁'⟩ := qmap_cast (Category.id_comp j₁).symm k₁
  obtain ⟨k₂', hk₂'⟩ := qmap_cast (Category.id_comp j₂).symm k₂
  obtain ⟨m₁, hm₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Y₁ s s₀ t₁ a o₁ u₁ (𝟙 V) j₁).2.2.1 inferInstance n₁ k₁'
  obtain ⟨m₂, hm₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Y₂ s s₀ t₂ a' o₂ u₂ (𝟙 V) j₂).2.2.1 inferInstance n₂ k₂'
  obtain ⟨mx, hmx⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mf
  obtain ⟨mz, hmz⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂ mπ
  obtain ⟨y, hy, m₀, m', hsq⟩ := read_tj Tj (j₁ ≫ f) s₀ hb₁ o₁ o₂ mx ψ₀ hu hi ht
  obtain ⟨e₁, he₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m' Tj.mt
  obtain ⟨e₀, he₀⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀ Tj.ms
  have hbt : (y ≫ Tj.t) ≫ M.s = s₀ := by
    rw [Category.assoc, ← Tj.st, ← Category.assoc, hy, hb₁]
  have yt : y ≫ Tj.t = j₂ ≫ π := (M.rep V s₀ o₂).unique ⟨hbt, ⟨e₁⟩⟩ ⟨hb₂, ⟨mz⟩⟩
  obtain ⟨p₁, hp₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Tj.Y s s₀ (Tj.s ≫ M.s) a o₁ Tj.o (𝟙 V) y).1 n₁ m₀
  obtain ⟨p₂, hp₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Tj.Y s s₀ (Tj.s ≫ M.s) a' o₂ Tj.o' (𝟙 V) y).1 n₂ m'
  have r₀ : m₀.φ ≫ Tj.ms.φ = m₁.φ ≫ mf.φ := by
    rw [← he₀, ← hmx]
    exact rigid_of hO hN hNq e₀ mx hy
  have r₁ : m'.φ ≫ Tj.mt.φ = m₂.φ ≫ mπ.φ := by
    rw [← he₁, ← hmz]
    exact rigid_of hO hN hNq e₁ mz yt
  refine ⟨y, n₁.φ ≫ m₀.φ, n₂.φ ≫ m'.φ, hy, yt, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p₁', hp₁'⟩ := qmap_cast (Category.id_comp y) p₁
    have := p₁'.cart
    rw [hp₁', hp₁] at this
    exact this
  · obtain ⟨p₂', hp₂'⟩ := qmap_cast (Category.id_comp y) p₂
    have := p₂'.cart
    rw [hp₂', hp₂] at this
    exact this
  · rw [Category.assoc, hsq, ← Category.assoc, hψ, Category.assoc]
  · rw [Category.assoc, r₀, ← Category.assoc, ← hm₁, hk₁']
  · rw [Category.assoc, r₁, ← Category.assoc, ← hm₂, hk₂']

end

theorem UpperTheory.Gal.FiniteEtaleModels.bRead_of :
    IsogG → QObj → QComp → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → BRead := by
  intro hI hQO hQC hO p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hle hin h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂
    C₁ C₂ W f mf hf e he he0 Tj
  have h3 : 3 ≤ N₀ := X₁.lev.1
  have hcq : N₀.Coprime q := X₁.lev.2.1
  have hM₁ : M₁.1 = N₀ * c₁ := hn₁.1
  have hM₂ : M₂.1 = N₀ * c₂ := hn₂.1
  have pos₁ : 0 < M₁.1 := by have := M₁.2.1; omega
  have pos₂ : 0 < M₂.1 := by have := M₂.2.1; omega
  obtain ⟨o₁, ⟨n₁⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₁.1 N₀ c₁ hM₁ pos₁ hcq _ _ (T.M M₁).univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₂.1 N₀ c₂ hM₂ pos₂ hcq _ _ W.o
  obtain ⟨ψ₀, hψ, hi, ht⟩ := hI p D G L E gb q r 𝔴 𝔴' S.atq S.sp S.std.m1 hmax hu (Ow w) S.b N₀ hcq i e he h 1 htj hint (one_mem _) M₁ M₂ c₁ c₂
    hM₁ hM₂ _ _ (T.M M₁).univ W.o W.ψ (by rw [_root_.mul_one]; exact W.trans) _ o₁ o₂ n₁ n₂
  obtain ⟨k₂, hk₂⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ (T.M M₂).X X₂.Y.X X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s
    (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2 _ (T.M M₁).s W.o W.π W.φ C₂.m
  have hb₁ : (C₁.j ≫ f) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, hf]
    exact C₁.ov
  have hb₂ : ((W.π ≫ C₂.j) ≫ X₂.π) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, Category.assoc, X₂.ov]
    refine (congrArg (W.π ≫ ·) C₂.ov).trans ?_
    simp only [← Category.assoc, W.ov]
  have hun : IsUnit ((q : ℕ) : Γ((T.M M₁).X, ⊤)) := isUnit_nat_of (T.M M₁).s q (Fact.out : q.Prime).ne_zero
  obtain ⟨y, fa, fb, ys, yt, ca, cb, sq, ms, mt⟩ := read_core hQC hO h3 hcq Tj n₁ n₂ C₁.m k₂ mf X₂.mπ hb₁ hb₂ W.ψ.left ψ₀ hψ hun hi ht
  exact ⟨⟨y, ys, by rw [yt, Category.assoc], fa, fb, ca, cb, sq, ms, by rw [mt, hk₂, Category.assoc]⟩⟩
